// Deep terms (issue #13): every strategy keeps its pending work in the heap,
// so it finds and rewrites a position nested 100_000 levels deep on every
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
/// `Apply(head, [argument])` nested `depth` times in head position around
/// `leaf`.
fn head_chain(depth : Int, leaf : @syntax.Term[Int]) -> @syntax.Term[Int] {
  let mut term = leaf
  for _ in 0..<depth {
    term = Apply(term, [Value(0)])
  }
  term
}

///|
/// `Apply(Value(0), [Value(0), next])` nested `depth` times around `leaf`.
fn argument_chain(depth : Int, leaf : @syntax.Term[Int]) -> @syntax.Term[Int] {
  let mut term = leaf
  for _ in 0..<depth {
    term = Apply(Value(0), [Value(0), term])
  }
  term
}

///|
/// `Bind(x, next)` nested `depth` times around `leaf`.
fn binder_chain(depth : Int, leaf : @syntax.Term[Int]) -> @syntax.Term[Int] {
  let x = @core.Name::new("x")
  let mut term = leaf
  for _ in 0..<depth {
    term = Bind(x, term)
  }
  term
}

///|
/// The leaf of `head_chain(depth, _)`, `argument_chain(depth, _)` or
/// `binder_chain(depth, _)`, found with a loop.
fn chain_leaf(depth : Int, term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  let mut current = term
  for _ in 0..<depth {
    current = match current {
      Apply(head, [Value(0)]) => head
      Apply(Value(0), [Value(0), argument]) => argument
      Bind(_, body) => body
      _ => return None
    }
  }
  Some(current)
}

///|
/// Whether every frame of `path` is `frame` and there are `depth` of them.
fn is_uniform_path(
  path : @rewrite.ReductionPath,
  frame : @rewrite.ReductionFrame,
  depth : Int,
) -> Bool {
  let frames = path.to_array()
  frames.length() == depth && frames.iter().all(fn(each) { each == frame })
}

///|
test "deep terms: every strategy reaches the bottom of a head chain" {
  let rule = @rewrite.RuleName::unsafe_new("bump")
  let term = head_chain(DEPTH, Value(1))
  for
    strategy in [
      @eval.NormalOrder,
      @eval.ApplicativeOrder,
      @eval.WeakHead,
      @eval.FullNormal,
    ] {
    match @eval.reduce_once(term, rule, bump, strategy) {
      Reduced(before~, after~, path~, ..) => {
        assert_true(physical_equal(before, term))
        assert_true(is_uniform_path(path, ApplyHead, DEPTH))
        assert_true(chain_leaf(DEPTH, after) is Some(Value(2)))
      }
      NoStep => fail("the deep redex was not found")
    }
  }
}

///|
test "deep terms: argument and binder chains" {
  let rule = @rewrite.RuleName::unsafe_new("bump")
  for strategy in [@eval.NormalOrder, @eval.ApplicativeOrder] {
    match
      @eval.reduce_once(argument_chain(DEPTH, Value(1)), rule, bump, strategy) {
      Reduced(after~, path~, ..) => {
        assert_true(is_uniform_path(path, ApplyArgument(1), DEPTH))
        assert_true(chain_leaf(DEPTH, after) is Some(Value(2)))
      }
      NoStep => fail("the deep redex was not found")
    }
    match
      @eval.reduce_once(binder_chain(DEPTH, Value(1)), rule, bump, strategy) {
      Reduced(after~, path~, ..) => {
        assert_true(is_uniform_path(path, BinderBody, DEPTH))
        assert_true(chain_leaf(DEPTH, after) is Some(Value(2)))
      }
      NoStep => fail("the deep redex was not found")
    }
  }
  // weak-head reduction does not look inside arguments or binders
  assert_true(
    @eval.reduce_once(argument_chain(DEPTH, Value(1)), rule, bump, WeakHead)
    is NoStep,
  )
  for strategy in [@eval.NormalOrder, @eval.ApplicativeOrder, @eval.WeakHead] {
    assert_true(
      @eval.reduce_once(head_chain(DEPTH, Value(3)), rule, bump, strategy)
      is NoStep,
    )
    assert_true(
      @eval.reduce_once(argument_chain(DEPTH, Value(3)), rule, bump, strategy)
      is NoStep,
    )
  }
}

///|
test "deep terms: applicative order tries a deep application early" {
  // the rule rewrites applications whose first argument is `Value(5)`; it
  // applies to the prefix `Apply(Value(0), [Value(5)])` of every level, so
  // each level is tried right after its first argument, before the deeper
  // second argument, and the outermost level is rewritten
  let rule = @rewrite.RuleName::unsafe_new("first_five")
  let first_five = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Apply(Value(0), [Value(5), ..]) => Some(Value(9))
      _ => None
    }
  }
  let mut term : @syntax.Term[Int] = Value(1)
  for _ in 0..<DEPTH {
    term = Apply(Value(0), [Value(5), term])
  }
  match @eval.reduce_once(term, rule, first_five, ApplicativeOrder) {
    Reduced(after=Value(9), path~, ..) => assert_eq(path.length(), 0)
    _ => fail("the outermost application was not rewritten")
  }
  // with a rule that matches every prefix but no whole application, each
  // level is tried once early and the search goes on to the bottom
  let prefix_only = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Apply(Value(0), [Value(5)]) => Some(Value(9))
      Value(1) => Some(Value(2))
      _ => None
    }
  }
  match @eval.reduce_once(term, rule, prefix_only, ApplicativeOrder) {
    Reduced(path~, ..) =>
      assert_true(is_uniform_path(path, ApplyArgument(1), DEPTH))
    NoStep => fail("the deep redex was not found")
  }
}

///|
test "deep terms: evaluate and trace repeat deep steps" {
  let rule = @rewrite.RuleName::unsafe_new("count")
  let count = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Value(1) => Some(Value(2))
      Value(2) => Some(Value(3))
      _ => None
    }
  }
  let term = head_chain(DEPTH, Value(1))
  for strategy in [@eval.NormalOrder, @eval.ApplicativeOrder, @eval.WeakHead] {
    match @eval.evaluate(term, rule, count, strategy, 10) {
      NormalForm(term=normal, steps=2) =>
        assert_true(chain_leaf(DEPTH, normal) is Some(Value(3)))
      _ => fail("expected a normal form after two steps")
    }
    let reduction_trace = @eval.trace(term, rule, count, strategy, 10)
    assert_eq(reduction_trace.steps().length(), 2)
  }
}
