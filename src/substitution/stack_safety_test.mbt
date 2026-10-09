// Stack safety in the nesting depth (issue #13).
//
// Substitution runs on terms, and with replacements, nested `DEEP_DEPTH`
// levels deep in each of the shapes below, on every backend. The expected
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
/// Builds a node of `shape` nested `DEEP_DEPTH` levels deep over any
/// binding-aware AST. Occurrences of the free variable are `x`; binders are
/// named `z`; `value(i)` is an opaque leaf.
fn[N : @syntax.BindingSyntax] deep_node(
  shape : DeepShape,
  x : N,
  z : @core.Name,
  value : (Int) -> N,
) -> N {
  let mut node = x
  for i in 0..<DEEP_DEPTH {
    node = match shape {
      HeadChain => @syntax.BindingSyntax::apply(node, [value(i)])
      ArgumentChain => @syntax.BindingSyntax::apply(x, [node])
      BindChain => @syntax.BindingSyntax::bind(z, node)
      Mixed =>
        match i % 3 {
          0 => @syntax.BindingSyntax::bind(z, node)
          1 => @syntax.BindingSyntax::apply(node, [value(i)])
          _ =>
            @syntax.BindingSyntax::apply(x, [
              @syntax.BindingSyntax::variable(z),
              node,
            ])
        }
    }
  }
  node
}

///|
fn deep_term(
  shape : DeepShape,
  x : @syntax.Term[Int],
  z : @core.Name,
) -> @syntax.Term[Int] {
  deep_node(shape, x, z, fn(i) { @syntax.Term::Value(i) })
}

///|
/// Minimal downstream AST for the generic substitution.
priv enum DeepMock {
  Leaf(Int)
  Name(@core.Name)
  Node(DeepMock, Array[DeepMock])
  Scope(@core.Name, DeepMock)
}

///|
impl @syntax.BindingSyntax for DeepMock with fn project(self) {
  match self {
    Leaf(_) => @syntax.BindingView::Opaque
    Name(name) => @syntax.BindingView::Variable(name)
    Node(head, arguments) => @syntax.BindingView::Apply(head, arguments)
    Scope(name, body) => @syntax.BindingView::Bind(name, body)
  }
}

///|
impl @syntax.BindingSyntax for DeepMock with fn variable(name) {
  Name(name)
}

///|
impl @syntax.BindingSyntax for DeepMock with fn apply(head, arguments) {
  Node(head, arguments)
}

///|
impl @syntax.BindingSyntax for DeepMock with fn bind(name, body) {
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
  deep_node(shape, x, z, fn(i) { DeepMock::Leaf(i) })
}

///|
test "deep terms: substitution" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let replacement : @syntax.Term[Int] = Apply(Variable(y), [Value(-1)])
  let substitution = @substitution.Substitution::singleton(x, replacement)
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    assert_true(substitution.apply(term) == deep_term(shape, replacement, z))
  }
}

///|
test "deep terms: substitution freshens a capturing binder" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let z = @core.Name::new("z")
  let substitution : @substitution.Substitution[Int] = @substitution.Substitution::singleton(
    x,
    Variable(y),
  )
  // the outermost binder captures `y`: it is freshened and the whole deep
  // body is alpha-renamed before the substitution continues
  for shape in deep_shapes {
    let term : @syntax.Term[Int] = Bind(
      y,
      Apply(Variable(y), [deep_term(shape, Variable(x), z)]),
    )
    let expected : @syntax.Term[Int] = Bind(
      y1,
      Apply(Variable(y1), [deep_term(shape, Variable(y), z)]),
    )
    assert_true(substitution.apply(term) == expected)
  }
}

///|
test "deep terms: deep replacements" {
  let x = @core.Name::new("x")
  let w = @core.Name::new("w")
  let z = @core.Name::new("z")
  let z1 = @core.Name::new("z_1")
  let term : @syntax.Term[Int] = Bind(z, Apply(Variable(x), [Variable(z)]))
  for shape in deep_shapes {
    // the replacement mentions `z` free, so the binder is freshened
    let replacement : @syntax.Term[Int] = Apply(Variable(z), [
      deep_term(shape, Variable(w), z),
    ])
    let substitution = @substitution.Substitution::singleton(x, replacement)
    let expected : @syntax.Term[Int] = Bind(
      z1,
      Apply(replacement, [Variable(z1)]),
    )
    assert_true(substitution.apply(term) == expected)
  }
}

///|
test "deep terms: composition and renamings" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let first = @substitution.from_renaming([x], @core.Renaming::singleton(x, y))
  let second = @substitution.Substitution::singleton(y, @syntax.Value(5))
  for shape in deep_shapes {
    let term = deep_term(shape, Variable(x), z)
    let renamed = first.apply(term)
    assert_true(renamed == deep_term(shape, Variable(y), z))
    let expected = deep_term(shape, Value(5), z)
    assert_true(second.apply(renamed) == expected)
    assert_true(first.then(second).apply(term) == expected)
  }
}

///|
test "deep terms: generic substitution" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let z = @core.Name::new("z")
  let constant = @substitution.GenericSubstitution::singleton(x, Leaf(-1))
  let renaming = @substitution.GenericSubstitution::singleton(x, Name(y))
  for shape in deep_shapes {
    let node = deep_mock(shape, Name(x), z)
    assert_true(
      mock_equal(constant.apply_once(node), deep_mock(shape, Leaf(-1), z)),
    )
    // capture at the outermost binder
    let capturing = Scope(y, Node(Name(y), [node]))
    let expected = Scope(y1, Node(Name(y1), [deep_mock(shape, Name(y), z)]))
    assert_true(mock_equal(renaming.apply_once(capturing), expected))
  }
}
