// Deep terms (issue #13): the traversals keep their pending work in the heap,
// so they find and rewrite a position nested 100_000 levels deep on every
// backend. The checks below walk the results with loops instead of `==` or
// `Debug`, which are recursive.

///|
const DEPTH : Int = 100_000

///|
/// `Value(1)` is the only redex: it becomes `Value(2)`.
fn bump(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  match term {
    Value(1) => Some(Value(2))
    _ => None
  }
}

///|
/// The shapes of nesting: the next level goes through the head of a unary
/// application, its second argument, or the body of a binder.
priv enum Shape {
  Heads
  Arguments
  Binders
  Mixed
}

///|
/// The frame that enters level `level` of a term of the given shape.
fn frame_at(shape : Shape, level : Int) -> @rewrite.ReductionFrame {
  match shape {
    Heads => ApplyHead
    Arguments => ApplyArgument(1)
    Binders => BinderBody
    Mixed =>
      match level % 3 {
        0 => ApplyHead
        1 => ApplyArgument(1)
        _ => BinderBody
      }
  }
}

///|
/// A term with `leaf` nested `depth` levels deep, every level entered by
/// `frame_at(shape, level)`. The other children are `Value(0)`.
fn nest(
  shape : Shape,
  depth : Int,
  leaf : @syntax.Term[Int],
) -> @syntax.Term[Int] {
  let x = @core.Name::new("x")
  let mut term = leaf
  for level = depth - 1; level >= 0; level = level - 1 {
    term = match frame_at(shape, level) {
      ApplyHead => Apply(term, [Value(0)])
      ApplyArgument(_) => Apply(Value(0), [Value(0), term])
      BinderBody => Bind(x, term)
    }
  }
  term
}

///|
/// Follows `depth` levels of `nest(shape, depth, _)` down from `term` and
/// returns the leaf, or `None` if the term does not have that shape.
fn leaf_of(
  shape : Shape,
  depth : Int,
  term : @syntax.Term[Int],
) -> @syntax.Term[Int]? {
  let mut current = term
  for level in 0..<depth {
    current = match (frame_at(shape, level), current) {
      (ApplyHead, Apply(head, [Value(0)])) => head
      (ApplyArgument(_), Apply(Value(0), [Value(0), argument])) => argument
      (BinderBody, Bind(_, body)) => body
      _ => return None
    }
  }
  Some(current)
}

///|
/// Whether `path` is the path of `nest(shape, depth, _)` to its leaf.
fn is_leaf_path(
  shape : Shape,
  depth : Int,
  path : @rewrite.ReductionPath,
) -> Bool {
  let frames = path.to_array()
  if frames.length() != depth {
    return false
  }
  for level in 0..<depth {
    if frames[level] != frame_at(shape, level) {
      return false
    }
  }
  true
}

///|
test "deep terms: one step finds and rewrites the deepest position" {
  let rule = @rewrite.RuleName::unsafe_new("bump")
  for shape in [Heads, Arguments, Binders, Mixed] {
    let term = nest(shape, DEPTH, Value(1))
    for strategy in 0..<3 {
      let step = match strategy {
        0 => @rewrite.top_down_once(term, rule, bump)
        1 => @rewrite.bottom_up_once(term, rule, bump)
        _ =>
          match @rewrite.generic_top_down_once(term, rule, bump) {
            NoStep => NoStep
            Reduced(before~, after~, rule~, path~) =>
              Reduced(before~, after~, rule~, path~)
          }
      }
      match step {
        Reduced(before~, after~, path~, ..) => {
          assert_true(physical_equal(before, term))
          assert_true(is_leaf_path(shape, DEPTH, path))
          assert_true(leaf_of(shape, DEPTH, after) is Some(Value(2)))
        }
        NoStep => fail("the deep redex was not found")
      }
    }
  }
}

///|
test "deep terms: a search without a redex ends with NoStep" {
  let rule = @rewrite.RuleName::unsafe_new("bump")
  for shape in [Heads, Arguments, Binders, Mixed] {
    let term = nest(shape, DEPTH, Value(3))
    assert_true(@rewrite.top_down_once(term, rule, bump) is NoStep)
    assert_true(@rewrite.bottom_up_once(term, rule, bump) is NoStep)
    assert_true(@rewrite.generic_top_down_once(term, rule, bump) is NoStep)
  }
}

///|
test "deep terms: post-order rewrites the innermost application first" {
  // every application is a redex; bottom-up picks the deepest one
  let rule = @rewrite.RuleName::unsafe_new("collapse")
  let collapse = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Apply(_, _) => Some(Value(7))
      _ => None
    }
  }
  let term = nest(Arguments, DEPTH, Value(1))
  match @rewrite.bottom_up_once(term, rule, collapse) {
    Reduced(after~, path~, ..) => {
      assert_true(is_leaf_path(Arguments, DEPTH - 1, path))
      assert_true(leaf_of(Arguments, DEPTH - 1, after) is Some(Value(7)))
    }
    NoStep => fail("no application rewritten")
  }
  match @rewrite.top_down_once(term, rule, collapse) {
    Reduced(after=Value(7), path~, ..) => assert_eq(path.length(), 0)
    _ => fail("the root application was not rewritten")
  }
}

///|
test "deep terms: normalize and trace repeat deep steps" {
  // `Value(1)` -> `Value(2)` -> `Value(3)` at the bottom of each shape
  let rule = @rewrite.RuleName::unsafe_new("count")
  let count = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Value(1) => Some(Value(2))
      Value(2) => Some(Value(3))
      _ => None
    }
  }
  for shape in [Heads, Arguments, Binders, Mixed] {
    let term = nest(shape, DEPTH, Value(1))
    let step = fn(current) { @rewrite.top_down_once(current, rule, count) }
    match @rewrite.normalize(term, step, 10) {
      NormalForm(term=normal, steps=2) =>
        assert_true(leaf_of(shape, DEPTH, normal) is Some(Value(3)))
      _ => fail("expected a normal form after two steps")
    }
    let reduction_trace = @rewrite.trace(term, step, 10)
    let steps = reduction_trace.steps()
    assert_eq(steps.length(), 2)
    for recorded in steps {
      match recorded {
        Reduced(path~, ..) => assert_true(is_leaf_path(shape, DEPTH, path))
        NoStep => fail("trace records only successful steps")
      }
    }
    match @rewrite.generic_normalize(term, rule, count, 1) {
      StepLimitReached(term=current, steps=1) =>
        assert_true(leaf_of(shape, DEPTH, current) is Some(Value(2)))
      _ => fail("expected the step limit after one step")
    }
  }
}

///|
test "deep paths are built by prepending in linear time" {
  let mut path = @rewrite.ReductionPath::root()
  for _ in 0..<DEPTH {
    path = path.prepend(ApplyHead)
  }
  let longer = path.prepend(BinderBody)
  let branch = path.prepend(ApplyArgument(0))
  assert_eq(path.length(), DEPTH)
  assert_eq(longer.length(), DEPTH + 1)
  assert_true(longer.to_array()[0] == BinderBody)
  assert_true(branch.to_array()[0] == ApplyArgument(0))
  assert_true(longer != branch)
  assert_true(path.to_array()[0] == ApplyHead)
}
