///|
/// Structured single-step result for a downstream binding-aware AST.
pub(all) enum GenericStepResult[N] {
  NoStep
  Reduced(before~ : N, after~ : N, rule~ : RuleName, path~ : ReductionPath)
} derive(Eq, Debug)

///|
/// Bounded generic rewrite result.
pub(all) enum GenericNormalizationResult[N] {
  NormalForm(term~ : N, steps~ : Int)
  StepLimitReached(term~ : N, steps~ : Int)
} derive(Eq, Debug)

///|
fn[N] lift_generic_step(
  before : N,
  result : GenericStepResult[N],
  frame : ReductionFrame,
  rebuild : (N) -> N,
) -> GenericStepResult[N] {
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
/// Rewrites at most one downstream AST node in pre-order.
pub fn[N : @syntax.BindingSyntax] generic_top_down_once(
  node : N,
  rule_name : RuleName,
  rule : (N) -> N?,
) -> GenericStepResult[N] {
  match rule(node) {
    Some(after) =>
      Reduced(before=node, after~, rule=rule_name, path=ReductionPath::root())
    None =>
      match @syntax.BindingSyntax::project(node) {
        @syntax.BindingView::Opaque | @syntax.BindingView::Variable(_) => NoStep
        @syntax.BindingView::Bind(name, body) =>
          lift_generic_step(
            node,
            generic_top_down_once(body, rule_name, rule),
            BinderBody,
            fn(next) { @syntax.BindingSyntax::bind(name, next) },
          )
        @syntax.BindingView::Apply(head, arguments) => {
          let head_step = generic_top_down_once(head, rule_name, rule)
          match head_step {
            Reduced(_) =>
              lift_generic_step(node, head_step, ApplyHead, fn(next) {
                @syntax.BindingSyntax::apply(next, arguments)
              })
            NoStep => {
              for i in 0..<arguments.length() {
                let argument_step = generic_top_down_once(
                  arguments[i],
                  rule_name,
                  rule,
                )
                match argument_step {
                  Reduced(_) =>
                    return lift_generic_step(
                      node,
                      argument_step,
                      ApplyArgument(i),
                      fn(next) {
                        let next_arguments = arguments.copy()
                        next_arguments[i] = next
                        @syntax.BindingSyntax::apply(head, next_arguments)
                      },
                    )
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
/// Repeats only `generic_top_down_once` until stable or bounded.
pub fn[N : @syntax.BindingSyntax] generic_normalize(
  node : N,
  rule_name : RuleName,
  rule : (N) -> N?,
  max_steps : Int,
) -> GenericNormalizationResult[N] {
  let mut current = node
  let mut steps = 0
  while steps < max_steps {
    match generic_top_down_once(current, rule_name, rule) {
      NoStep =>
        return GenericNormalizationResult::NormalForm(term=current, steps~)
      Reduced(after~, ..) => {
        current = after
        steps = steps + 1
      }
    }
  }
  match generic_top_down_once(current, rule_name, rule) {
    NoStep => GenericNormalizationResult::NormalForm(term=current, steps~)
    Reduced(_) =>
      GenericNormalizationResult::StepLimitReached(term=current, steps~)
  }
}
