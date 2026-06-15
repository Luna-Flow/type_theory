///|
/// Minimal binding-aware view used by generic semantic algorithms.
pub(all) enum BindingView[N] {
  Opaque
  Variable(@core.Name)
  Apply(N, Array[N])
  Bind(@core.Name, N)
}

///|
/// Open extension point for downstream binding-aware ASTs.
pub(open) trait BindingSyntax {
  fn project(Self) -> BindingView[Self]
  fn variable(@core.Name) -> Self
  fn apply(Self, Array[Self]) -> Self
  fn bind(@core.Name, Self) -> Self
}

///|
pub impl[T] BindingSyntax for Term[T] with fn project(self) {
  match self {
    Term::Value(_) => BindingView::Opaque
    Term::Variable(name) => BindingView::Variable(name)
    Term::Apply(head, arguments) => BindingView::Apply(head, arguments)
    Term::Bind(name, body) => BindingView::Bind(name, body)
  }
}

///|
pub impl[T] BindingSyntax for Term[T] with fn variable(name) {
  Term::Variable(name)
}

///|
pub impl[T] BindingSyntax for Term[T] with fn apply(head, arguments) {
  Term::Apply(head, arguments)
}

///|
pub impl[T] BindingSyntax for Term[T] with fn bind(name, body) {
  Term::Bind(name, body)
}

///|
fn[N : BindingSyntax] generic_free_variables_visit(
  current : N,
  bound : @hashset.HashSet[@core.Name],
) -> @hashset.HashSet[@core.Name] {
  match BindingSyntax::project(current) {
    BindingView::Opaque => @hashset.new()
    BindingView::Variable(name) =>
      if bound.contains(name) {
        @hashset.new()
      } else {
        @hashset.from_array([name])
      }
    BindingView::Apply(head, arguments) => {
      let mut result = generic_free_variables_visit(head, bound)
      for argument in arguments {
        result = result.union(generic_free_variables_visit(argument, bound))
      }
      result
    }
    BindingView::Bind(name, body) =>
      generic_free_variables_visit(body, bound.add(name))
  }
}

///|
/// Returns free variables for any AST implementing `BindingSyntax`.
pub fn[N : BindingSyntax] generic_free_variables(
  node : N,
) -> @hashset.HashSet[@core.Name] {
  generic_free_variables_visit(node, @hashset.new())
}

///|
/// Returns all names mentioned by a binding-aware AST.
pub fn[N : BindingSyntax] generic_all_names(
  node : N,
) -> @hashset.HashSet[@core.Name] {
  match BindingSyntax::project(node) {
    BindingView::Opaque => @hashset.new()
    BindingView::Variable(name) => @hashset.from_array([name])
    BindingView::Apply(head, arguments) => {
      let mut result = generic_all_names(head)
      for argument in arguments {
        result = result.union(generic_all_names(argument))
      }
      result
    }
    BindingView::Bind(name, body) => generic_all_names(body).add(name)
  }
}

///|
fn[N : BindingSyntax] generic_rename_bound_visit(
  node : N,
  active : Bool,
  from : @core.Name,
  to_ : @core.Name,
) -> N {
  match BindingSyntax::project(node) {
    BindingView::Opaque => node
    BindingView::Variable(name) =>
      if active && name == from {
        BindingSyntax::variable(to_)
      } else {
        node
      }
    BindingView::Apply(head, arguments) =>
      BindingSyntax::apply(
        generic_rename_bound_visit(head, active, from, to_),
        arguments.map(fn(argument) {
          generic_rename_bound_visit(argument, active, from, to_)
        }),
      )
    BindingView::Bind(name, body) =>
      BindingSyntax::bind(
        name,
        generic_rename_bound_visit(body, active && name != from, from, to_),
      )
  }
}

///|
/// Checked alpha-renaming for downstream binding-aware ASTs.
pub fn[N : BindingSyntax] generic_alpha_rename_bound(
  node : N,
  from : @core.Name,
  to_ : @core.Name,
) -> N? {
  if from == to_ {
    Some(node)
  } else if generic_all_names(node).contains(to_) {
    None
  } else {
    Some(generic_rename_bound_visit(node, true, from, to_))
  }
}
