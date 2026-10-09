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
/// Rewrites at most one downstream AST node in pre-order.
pub fn[N : @syntax.BindingSyntax] generic_top_down_once(
  node : N,
  rule_name : RuleName,
  rule : (N) -> N?,
) -> GenericStepResult[N] {
  match search_top_down(node, rule) {
    None => NoStep
    Some(found) => {
      let (after, path) = found.rebuild()
      Reduced(before=node, after~, rule=rule_name, path~)
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
