// Stack safety in the nesting depth (issue #13).
//
// Every public operation of the package runs on terms nested `deep_depth`
// levels deep, in each of the shapes below, on every backend. The expected
// results are built by the same loop that builds the input, so the checks
// compare with the stack-safe `==` and never format a deep term (`Debug` of
// a deep term is not stack-safe).

///|
const DEEP_DEPTH : Int = 100_000

///|
/// The nesting shapes exercised by the deep tests.
priv enum DeepShape {
  /// `((x v0) v1) ...`: an `Apply` chain in head position
  HeadChain
  /// `x (x (x ...))`: an `Apply` chain in argument position
  ArgumentChain
  /// `λz. λz. ... x`: a `Bind` chain
  BindChain
  /// binders, head and argument positions in turn
  Mixed
}

///|
let deep_shapes : Array[DeepShape] = [
  HeadChain,
  ArgumentChain,
  BindChain,
  Mixed,
]

///|
/// Builds a term of `shape` nested `depth` levels deep over any
/// binding-aware AST. Occurrences of the free variable are `x`; binders are
/// named `z`; `value(i)` is an opaque leaf.
fn[N : BindingSyntax] deep_node(
  shape : DeepShape,
  depth : Int,
  x : N,
  z : @core.Name,
  value : (Int) -> N,
) -> N {
  let mut node = x
  for i in 0..<depth {
    node = match shape {
      HeadChain => BindingSyntax::apply(node, [value(i)])
      ArgumentChain => BindingSyntax::apply(x, [node])
      BindChain => BindingSyntax::bind(z, node)
      Mixed =>
        match i % 3 {
          0 => BindingSyntax::bind(z, node)
          1 => BindingSyntax::apply(node, [value(i)])
          _ => BindingSyntax::apply(x, [BindingSyntax::variable(z), node])
        }
    }
  }
  node
}

///|
/// `deep_node` over `Term[Int]`.
fn deep_term(
  shape : DeepShape,
  x : Term[Int],
  z : @core.Name,
  offset? : Int = 0,
) -> Term[Int] {
  deep_node(shape, DEEP_DEPTH, x, z, fn(i) { Term::Value(i + offset) })
}

///|
/// Minimal downstream AST for the generic algorithms.
priv enum DeepMock {
  Leaf(Int)
  Name(@core.Name)
  Node(DeepMock, Array[DeepMock])
  Scope(@core.Name, DeepMock)
}

///|
impl BindingSyntax for DeepMock with fn project(self) {
  match self {
    Leaf(_) => BindingView::Opaque
    Name(name) => BindingView::Variable(name)
    Node(head, arguments) => BindingView::Apply(head, arguments)
    Scope(name, body) => BindingView::Bind(name, body)
  }
}

///|
impl BindingSyntax for DeepMock with fn variable(name) {
  Name(name)
}

///|
impl BindingSyntax for DeepMock with fn apply(head, arguments) {
  Node(head, arguments)
}

///|
impl BindingSyntax for DeepMock with fn bind(name, body) {
  Scope(name, body)
}

///|
/// Structural equality of mock nodes with an explicit work stack.
fn mock_equal(left : DeepMock, right : DeepMock) -> Bool {
  let pending = [(left, right)]
  while pending.pop() is Some(pair) {
    match pair {
      (Leaf(a), Leaf(b)) => if a != b { return false }
      (Name(a), Name(b)) => if a != b { return false }
      (Node(a, a_args), Node(b, b_args)) => {
        if a_args.length() != b_args.length() {
          return false
        }
        pending.push((a, b))
        for i in 0..<a_args.length() {
          pending.push((a_args[i], b_args[i]))
        }
      }
      (Scope(a, a_body), Scope(b, b_body)) => {
        if a != b {
          return false
        }
        pending.push((a_body, b_body))
      }
      _ => return false
    }
  }
  true
}

///|
fn deep_mock(shape : DeepShape, x : DeepMock, z : @core.Name) -> DeepMock {
  deep_node(shape, DEEP_DEPTH, x, z, fn(i) { DeepMock::Leaf(i) })
}

///|
test "deep terms: structural equality" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  for shape in deep_shapes {
    let left = deep_term(shape, Variable(x), z)
    assert_true(left == deep_term(shape, Variable(x), z))
    // the innermost variable differs
    assert_true(left != deep_term(shape, Variable(y), z))
    match shape {
      // every binder differs
      BindChain | Mixed => assert_true(left != deep_term(shape, Variable(x), y))
      HeadChain | ArgumentChain => ()
    }
    match shape {
      // every value differs
      HeadChain | Mixed =>
        assert_true(left != deep_term(shape, Variable(x), z, offset=1))
      ArgumentChain | BindChain => ()
    }
  }
}

///|
/// `f (f (... (f v)))` nested `DEEP_DEPTH` levels deep.
fn[T] deep_spine(f : Term[T], v : Term[T]) -> Term[T] {
  let mut term = v
  for _ in 0..<DEEP_DEPTH {
    term = Apply(f, [term])
  }
  term
}

///|
test "deep terms: equality lifts the payload equality" {
  // as with the derived `==`, a term is not equal to itself when a payload
  // is not: there is no shortcut for physically equal subterms
  let f : Term[Double] = Variable(@core.Name::new("f"))
  let nan = deep_spine(f, Value(0.0 / 0.0))
  assert_false(nan == nan)
  assert_true(deep_spine(f, Value(0.0)) == deep_spine(f, Value(-0.0)))
}

///|
test "deep terms: map_values" {
  let x = @core.Name::new("x")
  let z = @core.Name::new("z")
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    let mapped = term.map_values(fn(value) { value + 1 })
    assert_true(mapped == deep_term(shape, Variable(x), z, offset=1))
  }
}

///|
test "deep terms: free_variables and all_names" {
  let x = @core.Name::new("x")
  let z = @core.Name::new("z")
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    // in `Mixed` every `z` is bound: the outermost level is a binder
    assert_true(free_variables(term) == @hashset.HashSet([x]))
    let names = all_names(term)
    match shape {
      HeadChain | ArgumentChain => assert_true(names == @hashset.HashSet([x]))
      BindChain | Mixed => assert_true(names == @hashset.HashSet([x, z]))
    }
  }
  // the innermost `x` is bound by the outermost of 100_000 binders
  let closed = Term::Bind(x, deep_term(BindChain, Variable(x), z))
  assert_true(free_variables(closed).is_empty())
}

///|
test "deep terms: alpha_equal" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let w = @core.Name::new("w")
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    assert_true(alpha_equal(term, term))
    assert_false(alpha_equal(term, deep_term(shape, Variable(y), z)))
    match shape {
      HeadChain | Mixed =>
        assert_false(
          alpha_equal(term, deep_term(shape, Variable(x), z, offset=1)),
        )
      ArgumentChain | BindChain => ()
    }
    // renaming every binder is invisible
    assert_true(alpha_equal(term, deep_term(shape, Variable(x), w)))
  }
  // the innermost variable refers to the outermost binder
  let left = Term::Bind(x, deep_term(BindChain, Variable(x), z))
  let right = Term::Bind(y, deep_term(BindChain, Variable(y), w))
  assert_true(alpha_equal(left, right))
  let inner = Term::Bind(x, deep_term(BindChain, Variable(z), z))
  assert_false(alpha_equal(left, inner))
}

///|
test "deep terms: rename_free" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let z = @core.Name::new("z")
  let renaming = @core.Renaming::singleton(x, y)
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    assert_true(term.rename_free(renaming) == deep_term(shape, Variable(y), z))
  }
  // capture at the outermost binder: the binder is freshened and the whole
  // deep body is alpha-renamed before the renaming continues
  for shape in deep_shapes {
    let term = Term::Bind(
      y,
      Apply(Variable(y), [deep_term(shape, Variable(x), z)]),
    )
    let expected = Term::Bind(
      y1,
      Apply(Variable(y1), [deep_term(shape, Variable(y), z)]),
    )
    assert_true(term.rename_free(renaming) == expected)
  }
}

///|
test "deep terms: alpha_rename_bound" {
  let x = @core.Name::new("x")
  let z = @core.Name::new("z")
  let w = @core.Name::new("w")
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    assert_true(
      term.alpha_rename_bound(x, w) == Some(deep_term(shape, Variable(w), z)),
    )
    match shape {
      // `z` occurs, so renaming to it could capture
      BindChain | Mixed => assert_true(term.alpha_rename_bound(x, z) is None)
      HeadChain | ArgumentChain => ()
    }
  }
  // an inner binder of the source name stops the renaming
  let shadowed = Term::Apply(Variable(x), [
    Bind(x, deep_term(ArgumentChain, Variable(x), z)),
  ])
  let expected = Term::Apply(Variable(w), [
    Bind(x, deep_term(ArgumentChain, Variable(x), z)),
  ])
  assert_true(shadowed.alpha_rename_bound(x, w) == Some(expected))
}

///|
test "deep terms: generic algorithms" {
  let x = @core.Name::new("x")
  let z = @core.Name::new("z")
  let w = @core.Name::new("w")
  for shape in deep_shapes {
    let node = deep_mock(shape, Name(x), z)
    assert_true(generic_free_variables(node) == @hashset.HashSet([x]))
    let names = generic_all_names(node)
    match shape {
      HeadChain | ArgumentChain => assert_true(names == @hashset.HashSet([x]))
      BindChain | Mixed => assert_true(names == @hashset.HashSet([x, z]))
    }
    match generic_alpha_rename_bound(node, x, w) {
      Some(renamed) =>
        assert_true(mock_equal(renamed, deep_mock(shape, Name(w), z)))
      None => fail("the target name does not occur")
    }
  }
}
