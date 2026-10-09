// Bounded-stack substitution (issue #13).
//
// `Substitution::apply` and `GenericSubstitution::apply_once` are one
// algorithm, specified by structural recursion over the binding view:
//
//   s(opaque)          = opaque
//   s(x)               = σ(x) if x ∈ dom σ, else x
//   s(h a1 ... an)     = s(h) s(a1) ... s(an)
//   s(bind y. b)       = bind y. σ∖y (b)                    if no capture
//                      = bind y'. (σ∖y)∖y' (b[y := y'])     otherwise
//
// where the binder captures when some `x ∈ dom(σ∖y)` occurs free in `b` and
// `y` occurs free in `σ(x)`, and `y'` is fresh for `σ∖y`, `b` and `y`.
//
// It runs as one loop over a heap array of pending work (the scheme of
// `@syntax`'s `rebuild`): `Visit` nodes in pre-order, head first, and
// assemble them in post-order from a heap array of results. The host stack
// depth is constant in the nesting depth of both the term and the
// replacements.
//
// The capture test is the old one, decided in a cheaper order: the free
// variables of each replacement are computed once per call instead of once
// per binder, and the free variables of the body only when some replacement
// in scope mentions the binder. The boolean is the same, so the result is.

///|
/// A substitution entry in scope, with the free variables of its
/// replacement.
priv struct Pending[N] {
  name : @core.Name
  replacement : N
  replacement_free : @hashset.HashSet[@core.Name]
}

///|
/// A pending step of `substitute`.
priv enum SubstituteTask[N] {
  /// Substitute into a node with the entries in scope and push the result.
  Visit(N, Array[Pending[N]])
  /// Pop the substituted head and `arity` substituted arguments (pushed in
  /// this order) and push their application.
  BuildApply(Int)
  /// Pop the substituted body and push it under a binder of this name.
  BuildBind(@core.Name)
}

///|
fn[N] without_name(
  scope : Array[Pending[N]],
  name : @core.Name,
) -> Array[Pending[N]] {
  scope.filter(fn(entry) { entry.name != name })
}

///|
/// Applies the entries as a simultaneous, one-pass, capture-avoiding
/// substitution. The entries have pairwise distinct names.
fn[N : @syntax.BindingSyntax] substitute(
  entries : Array[(@core.Name, N)],
  root : N,
) -> N {
  let scope = entries.map(fn(entry) {
    {
      name: entry.0,
      replacement: entry.1,
      replacement_free: @syntax.generic_free_variables(entry.1),
    }
  })
  let tasks : Array[SubstituteTask[N]] = [Visit(root, scope)]
  let results : Array[N] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(node, scope) =>
        match @syntax.BindingSyntax::project(node) {
          @syntax.BindingView::Opaque => results.push(node)
          @syntax.BindingView::Variable(name) => {
            let mut result = node
            for entry in scope {
              if entry.name == name {
                result = entry.replacement
                break
              }
            }
            results.push(result)
          }
          @syntax.BindingView::Apply(head, arguments) => {
            tasks.push(BuildApply(arguments.length()))
            for i = arguments.length() - 1; i >= 0; i = i - 1 {
              tasks.push(Visit(arguments[i], scope))
            }
            tasks.push(Visit(head, scope))
          }
          @syntax.BindingView::Bind(name, body) => {
            let under_binder = without_name(scope, name)
            if captures(under_binder, name, body) {
              let mut used = @syntax.generic_all_names(body).add(name)
              for entry in under_binder {
                used = used
                  .add(entry.name)
                  .union(@syntax.generic_all_names(entry.replacement))
              }
              let fresh = @core.fresh_name(name, used)
              match @syntax.generic_alpha_rename_bound(body, name, fresh) {
                Some(renamed_body) => {
                  tasks.push(BuildBind(fresh))
                  tasks.push(
                    Visit(renamed_body, without_name(under_binder, fresh)),
                  )
                }
                None => abort("fresh name unexpectedly occurs in the body")
              }
            } else {
              tasks.push(BuildBind(name))
              tasks.push(Visit(body, under_binder))
            }
          }
        }
      BuildApply(arity) => {
        let base = results.length() - arity
        let arguments = Array::makei(arity, fn(i) { results[base + i] })
        let head = results[base - 1]
        results.truncate(base - 1)
        results.push(@syntax.BindingSyntax::apply(head, arguments))
      }
      BuildBind(name) => {
        let body = results[results.length() - 1]
        results[results.length() - 1] = @syntax.BindingSyntax::bind(name, body)
      }
    }
  }
  results[0]
}

///|
/// Whether a binder `name` over `body` would capture a free variable of a
/// replacement in scope: some entry whose name occurs free in `body` has
/// `name` free in its replacement.
fn[N : @syntax.BindingSyntax] captures(
  scope : Array[Pending[N]],
  name : @core.Name,
  body : N,
) -> Bool {
  let candidates = scope.filter(fn(entry) {
    entry.replacement_free.contains(name)
  })
  if candidates.is_empty() {
    return false
  }
  let body_free = @syntax.generic_free_variables(body)
  candidates.iter().any(fn(entry) { body_free.contains(entry.name) })
}
