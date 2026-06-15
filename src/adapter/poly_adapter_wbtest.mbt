///|
/// Minimal polynomial-shaped AST used to verify downstream trait integration.
enum PolyExpr {
  Scalar(Int)
  Variable(@core.Name)
  Add(PolyExpr, Array[PolyExpr])
  Scope(@core.Name, PolyExpr)
} derive(Eq, Debug)

///|
impl @syntax.BindingSyntax for PolyExpr with fn project(self) {
  match self {
    Scalar(_) => @syntax.BindingView::Opaque
    Variable(name) => @syntax.BindingView::Variable(name)
    Add(head, rest) => @syntax.BindingView::Apply(head, rest)
    Scope(name, body) => @syntax.BindingView::Bind(name, body)
  }
}

///|
impl @syntax.BindingSyntax for PolyExpr with fn variable(name) {
  Variable(name)
}

///|
impl @syntax.BindingSyntax for PolyExpr with fn apply(head, arguments) {
  Add(head, arguments)
}

///|
impl @syntax.BindingSyntax for PolyExpr with fn bind(name, body) {
  Scope(name, body)
}

///|
test "downstream AST substitution is simultaneous and one pass" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let substitution = @substitution.GenericSubstitution::singleton(
    x,
    Variable(y),
  ).set(y, Scalar(2))
  let expression = Add(Variable(x), [Variable(y)])
  assert_true(
    substitution.apply_once(expression) == Add(Variable(y), [Scalar(2)]),
  )
}

///|
test "partial evaluation leaves unknown variables intact" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let substitution = @substitution.GenericSubstitution::singleton(x, Scalar(3))
  let expression = Add(Variable(x), [Variable(y)])
  assert_true(
    substitution.apply_once(expression) == Add(Scalar(3), [Variable(y)]),
  )
}

///|
test "downstream rewrite uses the shared structured traversal" {
  let expression = Add(Scalar(1), [Add(Scalar(0), [Scalar(2)])])
  let remove_zero = fn(node : PolyExpr) -> PolyExpr? {
    match node {
      Add(Scalar(0), [other]) => Some(other)
      _ => None
    }
  }
  match
    @rewrite.generic_top_down_once(
      expression,
      @rewrite.RuleName::unsafe_new("remove_zero"),
      remove_zero,
    ) {
    @rewrite.Reduced(after~, path~, ..) => {
      assert_true(after == Add(Scalar(1), [Scalar(2)]))
      assert_true(path.to_array() == [@rewrite.ApplyArgument(0)])
    }
    @rewrite.NoStep => assert_false(true)
  }
}
