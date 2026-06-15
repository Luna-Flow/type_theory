///|
/// Stable identifier for a reduction rule.
pub struct RuleName {
  value : String
} derive(Eq, Compare, Hash, Debug)

///|
/// Failures produced while validating a reduction rule name.
pub(all) enum RuleNameError {
  Empty
} derive(Eq, Debug)

///|
pub fn RuleName::new(value : String) -> Result[RuleName, RuleNameError] {
  if value.length() == 0 {
    Err(Empty)
  } else {
    Ok({ value, })
  }
}

///|
pub fn RuleName::unsafe_new(value : String) -> RuleName {
  match RuleName::new(value) {
    Ok(name) => name
    Err(Empty) => abort("reduction rule name must not be empty")
  }
}

///|
pub fn RuleName::value(self : RuleName) -> String {
  self.value
}

///|
/// One edge in a path from the root to a redex.
pub(all) enum ReductionFrame {
  BinderBody
  ApplyHead
  ApplyArgument(Int)
} derive(Eq, Debug)

///|
/// Root-to-redex path. The empty path identifies the root.
pub struct ReductionPath {
  frames : Array[ReductionFrame]
} derive(Eq, Debug)

///|
pub fn ReductionPath::root() -> ReductionPath {
  { frames: [] }
}

///|
pub fn ReductionPath::prepend(
  self : ReductionPath,
  frame : ReductionFrame,
) -> ReductionPath {
  let frames = [frame]
  frames.append(self.frames)
  { frames, }
}

///|
pub fn ReductionPath::to_array(self : ReductionPath) -> Array[ReductionFrame] {
  self.frames.copy()
}

///|
/// The result of exactly one reduction attempt.
pub(all) enum StepResult[T] {
  NoStep
  Reduced(
    before~ : @syntax.Term[T],
    after~ : @syntax.Term[T],
    rule~ : RuleName,
    path~ : ReductionPath
  )
} derive(Eq, Debug)

///|
/// The result of bounded repeated reduction.
pub(all) enum NormalizationResult[T] {
  NormalForm(term~ : @syntax.Term[T], steps~ : Int)
  StepLimitReached(term~ : @syntax.Term[T], steps~ : Int)
} derive(Eq, Debug)

///|
/// A complete bounded operational trace.
pub struct ReductionTrace[T] {
  initial : @syntax.Term[T]
  steps : Array[StepResult[T]]
  result : NormalizationResult[T]
} derive(Eq, Debug)

///|
pub fn[T] ReductionTrace::initial(self : ReductionTrace[T]) -> @syntax.Term[T] {
  self.initial
}

///|
pub fn[T] ReductionTrace::steps(
  self : ReductionTrace[T],
) -> Array[StepResult[T]] {
  self.steps.copy()
}

///|
pub fn[T] ReductionTrace::result(
  self : ReductionTrace[T],
) -> NormalizationResult[T] {
  self.result
}

///|
fn[T] lift_step(
  before : @syntax.Term[T],
  result : StepResult[T],
  frame : ReductionFrame,
  rebuild : (@syntax.Term[T]) -> @syntax.Term[T],
) -> StepResult[T] {
  match result {
    NoStep => NoStep
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
fn[T] top_down_step(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  match rule(term) {
    Some(after) =>
      Reduced(before=term, after~, rule=rule_name, path=ReductionPath::root())
    None =>
      match term {
        Value(_) | Variable(_) => NoStep
        Bind(name, body) =>
          lift_step(term, top_down_step(body, rule_name, rule), BinderBody, fn(
            next,
          ) {
            Bind(name, next)
          })
        Apply(head, arguments) => {
          let head_step = top_down_step(head, rule_name, rule)
          match head_step {
            Reduced(_) =>
              lift_step(term, head_step, ApplyHead, fn(next) {
                Apply(next, arguments)
              })
            NoStep => {
              for i in 0..<arguments.length() {
                let argument_step = top_down_step(arguments[i], rule_name, rule)
                match argument_step {
                  Reduced(_) =>
                    return lift_step(term, argument_step, ApplyArgument(i), fn(
                      next,
                    ) {
                      let next_arguments = arguments.copy()
                      next_arguments[i] = next
                      Apply(head, next_arguments)
                    })
                  NoStep => continue
                }
              }
              NoStep
            }
          }
        }
      }
  }
}

///|
fn[T] bottom_up_step(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  match term {
    Value(_) | Variable(_) =>
      match rule(term) {
        Some(after) =>
          Reduced(
            before=term,
            after~,
            rule=rule_name,
            path=ReductionPath::root(),
          )
        None => NoStep
      }
    Bind(name, body) => {
      let body_step = bottom_up_step(body, rule_name, rule)
      match body_step {
        Reduced(_) =>
          lift_step(term, body_step, BinderBody, fn(next) { Bind(name, next) })
        NoStep =>
          match rule(term) {
            Some(after) =>
              Reduced(
                before=term,
                after~,
                rule=rule_name,
                path=ReductionPath::root(),
              )
            None => NoStep
          }
      }
    }
    Apply(head, arguments) => {
      let head_step = bottom_up_step(head, rule_name, rule)
      match head_step {
        Reduced(_) =>
          lift_step(term, head_step, ApplyHead, fn(next) {
            Apply(next, arguments)
          })
        NoStep => {
          for i in 0..<arguments.length() {
            let argument_step = bottom_up_step(arguments[i], rule_name, rule)
            match argument_step {
              Reduced(_) =>
                return lift_step(term, argument_step, ApplyArgument(i), fn(
                  next,
                ) {
                  let next_arguments = arguments.copy()
                  next_arguments[i] = next
                  Apply(head, next_arguments)
                })
              NoStep => continue
            }
          }
          match rule(term) {
            Some(after) =>
              Reduced(
                before=term,
                after~,
                rule=rule_name,
                path=ReductionPath::root(),
              )
            None => NoStep
          }
        }
      }
    }
  }
}

///|
/// Rewrites the first matching node in pre-order.
pub fn[T] top_down_once(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  top_down_step(term, rule_name, rule)
}

///|
/// Rewrites the first matching node in post-order.
pub fn[T] bottom_up_once(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  bottom_up_step(term, rule_name, rule)
}

///|
/// Repeats a single-step reducer until no step exists or the limit is reached.
pub fn[T] normalize(
  term : @syntax.Term[T],
  step : (@syntax.Term[T]) -> StepResult[T],
  max_steps : Int,
) -> NormalizationResult[T] {
  let mut current = term
  let mut count = 0
  while count < max_steps {
    match step(current) {
      NoStep =>
        return NormalizationResult::NormalForm(term=current, steps=count)
      Reduced(after~, ..) => {
        current = after
        count = count + 1
      }
    }
  }
  match step(current) {
    NoStep => NormalizationResult::NormalForm(term=current, steps=count)
    Reduced(_) =>
      NormalizationResult::StepLimitReached(term=current, steps=count)
  }
}

///|
/// Records every successful step produced by the supplied reducer.
pub fn[T] trace(
  term : @syntax.Term[T],
  step : (@syntax.Term[T]) -> StepResult[T],
  max_steps : Int,
) -> ReductionTrace[T] {
  let initial = term
  let steps : Array[StepResult[T]] = []
  let mut current = term
  let mut count = 0
  while count < max_steps {
    match step(current) {
      NoStep =>
        return {
          initial,
          steps,
          result: NormalizationResult::NormalForm(term=current, steps=count),
        }
      Reduced(after~, ..) as reduced => {
        steps.push(reduced)
        current = after
        count = count + 1
      }
    }
  }
  let result = match step(current) {
    NoStep => NormalizationResult::NormalForm(term=current, steps=count)
    Reduced(_) =>
      NormalizationResult::StepLimitReached(term=current, steps=count)
  }
  { initial, steps, result }
}
