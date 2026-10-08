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
fn[T] lift_db_step(
  before : DbTerm[T],
  result : DbStepResult[T],
  frame : @rewrite.ReductionFrame,
  rebuild : (DbTerm[T]) -> DbTerm[T],
) -> DbStepResult[T] {
  match result {
    NoStep => NoStep
    ScopeFailure(error) => ScopeFailure(error)
    Reduced(after=child_after, rule~, path~, ..) =>
      Reduced(
        before~,
        after=rebuild(child_after),
        rule~,
        path=path.prepend(frame),
      )
  }
}

///|
/// Removes empty applications `Apply(h, [])` around a term; an application
/// with no arguments is read as its head.
fn[T] strip_empty_applications(term : DbTerm[T]) -> DbTerm[T] {
  match term {
    Apply(head, []) => strip_empty_applications(head)
    _ => term
  }
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
/// depth. Subterms under binders are visited with this function, not with
/// `reduce_once`, because their indices may point at the enclosing binders.
fn[T] reduce_valid(term : DbTerm[T]) -> DbStepResult[T] {
  match (term, redex_body(term)) {
    (Apply(_, arguments), Some(body)) =>
      match instantiate(body, arguments[0]) {
        Err(error) => ScopeFailure(error)
        Ok(reduced) => {
          let after = if arguments.length() == 1 {
            reduced
          } else {
            Apply(reduced, arguments[1:].to_owned())
          }
          Reduced(
            before=term,
            after~,
            rule=@rewrite.RuleName::unsafe_new("beta"),
            path=@rewrite.ReductionPath::root(),
          )
        }
      }
    (Value(_) | Free(_) | Bound(_), _) => NoStep
    (Bind(body), _) =>
      lift_db_step(term, reduce_valid(body), BinderBody, fn(next) { Bind(next) })
    (Apply(head, arguments), None) => {
      let head_step = reduce_valid(head)
      match head_step {
        Reduced(_) =>
          lift_db_step(term, head_step, ApplyHead, fn(next) {
            Apply(next, arguments)
          })
        ScopeFailure(error) => ScopeFailure(error)
        NoStep => {
          for i in 0..<arguments.length() {
            let argument_step = reduce_valid(arguments[i])
            match argument_step {
              Reduced(_) =>
                return lift_db_step(term, argument_step, ApplyArgument(i), fn(
                  next,
                ) {
                  let next_arguments = arguments.copy()
                  next_arguments[i] = next
                  Apply(head, next_arguments)
                })
              ScopeFailure(error) => return ScopeFailure(error)
              NoStep => continue
            }
          }
          NoStep
        }
      }
    }
  }
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
