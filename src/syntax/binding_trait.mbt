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
/// Returns free variables for any AST implementing `BindingSyntax`.
pub fn[N : BindingSyntax] generic_free_variables(
  node : N,
) -> @hashset.HashSet[@core.Name] {
  // each pending node carries the names bound above it
  let mut result = @hashset.new()
  let pending = [(node, @hashset.new())]
  while pending.pop() is Some((current, bound)) {
    match BindingSyntax::project(current) {
      BindingView::Opaque => ()
      BindingView::Variable(name) =>
        if !bound.contains(name) {
          result = result.add(name)
        }
      BindingView::Apply(head, arguments) => {
        for i = arguments.length() - 1; i >= 0; i = i - 1 {
          pending.push((arguments[i], bound))
        }
        pending.push((head, bound))
      }
      BindingView::Bind(name, body) => pending.push((body, bound.add(name)))
    }
  }
  result
}

///|
/// Returns all names mentioned by a binding-aware AST.
pub fn[N : BindingSyntax] generic_all_names(
  node : N,
) -> @hashset.HashSet[@core.Name] {
  let mut result = @hashset.new()
  let pending = [node]
  while pending.pop() is Some(current) {
    match BindingSyntax::project(current) {
      BindingView::Opaque => ()
      BindingView::Variable(name) => result = result.add(name)
      BindingView::Apply(head, arguments) => {
        for i = arguments.length() - 1; i >= 0; i = i - 1 {
          pending.push(arguments[i])
        }
        pending.push(head)
      }
      BindingView::Bind(name, body) => {
        result = result.add(name)
        pending.push(body)
      }
    }
  }
  result
}

///|
/// A pending step of `rebuild`.
priv enum RebuildTask[N, C] {
  /// Rebuild a node under a context and push the result.
  Visit(N, C)
  /// Pop the rebuilt head and `arity` rebuilt arguments (pushed in this
  /// order) and push their application.
  BuildApply(Int)
  /// Pop the rebuilt body and push it under a binder of this name.
  BuildBind(@core.Name)
}

///|
/// Rebuilds `root` bottom-up with an explicit work stack: the stack-safe form
/// of the structural recursion
///
/// ```text
/// go(opaque, c)        = opaque
/// go(x, c)             = variable(x, c)
/// go(h a1 ... an, c)   = go(h, c) go(a1, c) ... go(an, c)
/// go(bind y. b, c)     = bind y'. go(b', c')  where (y', b', c') = binder(y, b, c)
/// ```
///
/// `variable` and `binder` are called in the order of the recursion (pre-order,
/// head first, then arguments left to right), and the nodes are assembled in
/// post-order, so the result equals the recursive one. Rebuilt children wait
/// on a heap array of results until their parent is assembled.
fn[N : BindingSyntax, C] rebuild(
  root : N,
  context : C,
  variable : (N, @core.Name, C) -> N,
  binder : (@core.Name, N, C) -> (@core.Name, N, C),
) -> N {
  let tasks : Array[RebuildTask[N, C]] = [Visit(root, context)]
  let results : Array[N] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(node, context) =>
        match BindingSyntax::project(node) {
          BindingView::Opaque => results.push(node)
          BindingView::Variable(name) =>
            results.push(variable(node, name, context))
          BindingView::Apply(head, arguments) => {
            tasks.push(BuildApply(arguments.length()))
            for i = arguments.length() - 1; i >= 0; i = i - 1 {
              tasks.push(Visit(arguments[i], context))
            }
            tasks.push(Visit(head, context))
          }
          BindingView::Bind(name, body) => {
            let (name, body, context) = binder(name, body, context)
            tasks.push(BuildBind(name))
            tasks.push(Visit(body, context))
          }
        }
      BuildApply(arity) => {
        let base = results.length() - arity
        let arguments = Array::makei(arity, fn(i) { results[base + i] })
        let head = results[base - 1]
        results.truncate(base - 1)
        results.push(BindingSyntax::apply(head, arguments))
      }
      BuildBind(name) => {
        let body = results[results.length() - 1]
        results[results.length() - 1] = BindingSyntax::bind(name, body)
      }
    }
  }
  results[0]
}

///|
/// Renames the free occurrences of `from` to `to_` while `active`; a binder
/// of `from` shadows it below. The caller checks that `to_` is not captured.
fn[N : BindingSyntax] generic_rename_bound_visit(
  node : N,
  active : Bool,
  from : @core.Name,
  to_ : @core.Name,
) -> N {
  rebuild(
    node,
    active,
    fn(node, name, active) {
      if active && name == from {
        BindingSyntax::variable(to_)
      } else {
        node
      }
    },
    fn(name, body, active) { (name, body, active && name != from) },
  )
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
