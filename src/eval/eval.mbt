///|
/// Standard operational traversal choices.
pub(all) enum Strategy {
  NormalOrder
  ApplicativeOrder
  WeakHead
  FullNormal
} derive(Eq, Debug)

///|
fn[T] weak_head_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> @rewrite.StepResult[T] {
  match rule(term) {
    Some(after) =>
      Reduced(
        before=term,
        after~,
        rule=rule_name,
        path=@rewrite.ReductionPath::root(),
      )
    None =>
      match term {
        Apply(head, arguments) =>
          match weak_head_once(head, rule_name, rule) {
            Reduced(after=next_head, rule~, path~, ..) =>
              Reduced(
                before=term,
                after=Apply(next_head, arguments),
                rule~,
                path=path.prepend(ApplyHead),
              )
            NoStep => NoStep
          }
        _ => NoStep
      }
  }
}

///|
/// Performs at most one reduction according to the selected strategy.
pub fn[T] reduce_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
) -> @rewrite.StepResult[T] {
  match strategy {
    NormalOrder | FullNormal => @rewrite.top_down_once(term, rule_name, rule)
    ApplicativeOrder => @rewrite.bottom_up_once(term, rule_name, rule)
    WeakHead => weak_head_once(term, rule_name, rule)
  }
}

///|
/// Normalizes solely by repeatedly invoking `reduce_once`.
pub fn[T] evaluate(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
  max_steps : Int,
) -> @rewrite.NormalizationResult[T] {
  @rewrite.normalize(
    term,
    fn(current) { reduce_once(current, rule_name, rule, strategy) },
    max_steps,
  )
}

///|
/// Produces an auditable operational reduction trace.
pub fn[T] trace(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
  max_steps : Int,
) -> @rewrite.ReductionTrace[T] {
  @rewrite.trace(
    term,
    fn(current) { reduce_once(current, rule_name, rule, strategy) },
    max_steps,
  )
}
