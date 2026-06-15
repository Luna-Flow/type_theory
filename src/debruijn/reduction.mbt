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
/// Performs one leftmost-outermost beta reduction.
pub fn[T] reduce_once(term : DbTerm[T]) -> DbStepResult[T] {
  match term {
    Apply(Bind(body), arguments) if arguments.length() > 0 =>
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
    Value(_) | Free(_) | Bound(_) => NoStep
    Bind(body) =>
      lift_db_step(term, reduce_once(body), BinderBody, fn(next) { Bind(next) })
    Apply(head, arguments) => {
      let head_step = reduce_once(head)
      match head_step {
        Reduced(_) =>
          lift_db_step(term, head_step, ApplyHead, fn(next) {
            Apply(next, arguments)
          })
        ScopeFailure(error) => ScopeFailure(error)
        NoStep => {
          for i in 0..<arguments.length() {
            let argument_step = reduce_once(arguments[i])
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
/// Repeats `reduce_once` and never uses a second traversal implementation.
pub fn[T] normalize(
  term : DbTerm[T],
  max_steps : Int,
) -> DbNormalizationResult[T] {
  let mut current = term
  let mut steps = 0
  while steps < max_steps {
    match reduce_once(current) {
      NoStep => return NormalForm(term=current, steps~)
      ScopeFailure(error) => return ScopeFailure(term=current, error~, steps~)
      Reduced(after~, ..) => {
        current = after
        steps = steps + 1
      }
    }
  }
  match reduce_once(current) {
    NoStep => NormalForm(term=current, steps~)
    ScopeFailure(error) => ScopeFailure(term=current, error~, steps~)
    Reduced(_) => StepLimitReached(term=current, steps~)
  }
}
