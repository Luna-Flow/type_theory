///|
/// One operational reduction attempt over De Bruijn syntax.
pub(all) enum DbStepResult[T] {
  NoStep
  Reduced(
    before~ : DbTerm[T],
    after~ : DbTerm[T],
    rule~ : @rewrite.RuleName,
    path~ : @rewrite.ReductionPath
  )
  ScopeFailure(ScopeError)
} derive(Eq, Debug)

///|
/// Result of bounded De Bruijn reduction.
pub(all) enum DbNormalizationResult[T] {
  NormalForm(term~ : DbTerm[T], steps~ : Int)
  StepLimitReached(term~ : DbTerm[T], steps~ : Int)
  ScopeFailure(term~ : DbTerm[T], error~ : ScopeError, steps~ : Int)
} derive(Eq, Debug)

///|
/// Removes empty applications `Apply(h, [])` around a term; an application
/// with no arguments is read as its head.
fn[T] strip_empty_applications(term : DbTerm[T]) -> DbTerm[T] {
  let mut current = term
  while current is Apply(head, []) {
    current = head
  }
  current
}

///|
/// Returns the binder body of a beta redex `Apply(h, [a, ..])` whose head is
/// a `Bind`, possibly wrapped in empty applications.
fn[T] redex_body(term : DbTerm[T]) -> DbTerm[T]? {
  match term {
    Apply(head, arguments) if arguments.length() > 0 =>
      match strip_empty_applications(head) {
        Bind(body) => Some(body)
        _ => None
      }
    _ => None
  }
}

///|
/// Performs one leftmost-outermost beta reduction.
///
/// The term is validated first: an ill-scoped term gives `ScopeFailure`
/// instead of a step, wherever the bad index is.
pub fn[T] reduce_once(term : DbTerm[T]) -> DbStepResult[T] {
  match validate(term) {
    Err(error) => ScopeFailure(error)
    Ok(_) => reduce_valid(term)
  }
}

///|
/// One leftmost-outermost beta step on a term that is well scoped at some
/// depth. Subterms under binders are searched as part of this term, not with
/// `reduce_once`, because their indices may point at the enclosing binders.
///
/// The recursive definition tries the node itself, then searches the head
/// and the arguments from left to right, and enters binder bodies: the
/// contracted redex is the first redex in pre-order. The search walks the
/// term in that order, keeping the path from the root to the current node in
/// a heap array, and the reduct is rebuilt along the path, innermost frame
/// first, as the recursive calls would rebuild it on return.
fn[T] reduce_valid(term : DbTerm[T]) -> DbStepResult[T] {
  // the ancestors of `current`, outermost first, with the child taken:
  // -1 for the head of an application, `i` for its argument `i`, 0 for the
  // body of a binder
  let ancestors : Array[(DbTerm[T], Int)] = []
  let mut current = term
  while true {
    if redex_body(current) is Some(body) && current is Apply(_, arguments) {
      return contract(term, ancestors, body, arguments)
    }
    match current {
      Bind(body) => {
        ancestors.push((current, 0))
        current = body
      }
      Apply(head, _) => {
        ancestors.push((current, -1))
        current = head
      }
      Value(_) | Free(_) | Bound(_) =>
        // the subtree of `current` has no redex: go on with the next
        // argument of the nearest application with one left
        while true {
          match ancestors.pop() {
            None => return NoStep
            Some((Apply(_, arguments) as parent, child)) if child + 1 <
              arguments.length() => {
              ancestors.push((parent, child + 1))
              current = arguments[child + 1]
              break
            }
            Some(_) => continue
          }
        }
    }
  }
  NoStep
}

///|
/// Contracts the redex with binder body `body` and arguments `arguments`
/// found below `ancestors` in `term`, and rebuilds the term around the reduct.
fn[T] contract(
  term : DbTerm[T],
  ancestors : Array[(DbTerm[T], Int)],
  body : DbTerm[T],
  arguments : Array[DbTerm[T]],
) -> DbStepResult[T] {
  let reduced = match instantiate(body, arguments[0]) {
    Err(error) => return ScopeFailure(error)
    Ok(reduced) => reduced
  }
  let mut after = if arguments.length() == 1 {
    reduced
  } else {
    Apply(reduced, arguments[1:].to_owned())
  }
  let mut path = @rewrite.ReductionPath::root()
  for i = ancestors.length() - 1; i >= 0; i = i - 1 {
    let (parent, child) = ancestors[i]
    match parent {
      Bind(_) => {
        after = Bind(after)
        path = path.prepend(BinderBody)
      }
      Apply(head, parent_arguments) =>
        if child < 0 {
          after = Apply(after, parent_arguments)
          path = path.prepend(ApplyHead)
        } else {
          let next_arguments = parent_arguments.copy()
          next_arguments[child] = after
          after = Apply(head, next_arguments)
          path = path.prepend(ApplyArgument(child))
        }
      Value(_) | Free(_) | Bound(_) => abort("an ancestor has children")
    }
  }
  Reduced(
    before=term,
    after~,
    rule=@rewrite.RuleName::unsafe_new("beta"),
    path~,
  )
}

///|
/// Repeats one beta step and never uses a second traversal implementation.
///
/// The input is validated once: an ill-scoped term gives `ScopeFailure` with
/// `steps=0`. Reducts of a well-scoped term are well scoped, so the steps
/// themselves need no further validation.
pub fn[T] normalize(
  term : DbTerm[T],
  max_steps : Int,
) -> DbNormalizationResult[T] {
  match validate(term) {
    Err(error) => return ScopeFailure(term~, error~, steps=0)
    Ok(_) => ()
  }
  let mut current = term
  let mut steps = 0
  while steps < max_steps {
    match reduce_valid(current) {
      NoStep => return NormalForm(term=current, steps~)
      ScopeFailure(error) => return ScopeFailure(term=current, error~, steps~)
      Reduced(after~, ..) => {
        current = after
        steps = steps + 1
      }
    }
  }
  match reduce_valid(current) {
    NoStep => NormalForm(term=current, steps~)
    ScopeFailure(error) => ScopeFailure(term=current, error~, steps~)
    Reduced(_) => StepLimitReached(term=current, steps~)
  }
}
