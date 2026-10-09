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
fn[T] root_step(
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
    None => NoStep
  }
}

///|
fn[T] lift_child_step(
  before : @syntax.Term[T],
  result : @rewrite.StepResult[T],
  frame : @rewrite.ReductionFrame,
  rebuild : (@syntax.Term[T]) -> @syntax.Term[T],
) -> @rewrite.StepResult[T] {
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
/// Leftmost-innermost search on the curried reading of application spines.
///
/// `Apply(h, [a0, ..., an])` is read as `(...((h a0) a1) ...) an`. Post-order
/// on that reading visits `h`, `a0`, the prefix `h a0`, `a1`, the prefix
/// `h a0 a1`, and so on. Only the whole application is a position of the
/// n-ary tree, so a prefix is never rewritten on its own: after argument `i`,
/// if the rule applies to the prefix `Apply(h, [a0, ..., ai])`, the rule is
/// tried on the whole application at this point instead of after the last
/// argument. The reported step is therefore always the rule applied at a real
/// position, and every position is still tried.
fn[T] applicative_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> @rewrite.StepResult[T] {
  match term {
    Value(_) | Variable(_) => root_step(term, rule_name, rule)
    Bind(name, body) =>
      match applicative_once(body, rule_name, rule) {
        Reduced(_) as body_step =>
          lift_child_step(term, body_step, BinderBody, fn(next) {
            Bind(name, next)
          })
        NoStep => root_step(term, rule_name, rule)
      }
    Apply(head, arguments) => {
      match applicative_once(head, rule_name, rule) {
        Reduced(_) as head_step =>
          return lift_child_step(term, head_step, ApplyHead, fn(next) {
            Apply(next, arguments)
          })
        NoStep => ()
      }
      let last = arguments.length() - 1
      let mut root_failed = false
      for i in 0..<arguments.length() {
        match applicative_once(arguments[i], rule_name, rule) {
          Reduced(_) as argument_step =>
            return lift_child_step(term, argument_step, ApplyArgument(i), fn(
              next,
            ) {
              let next_arguments = arguments.copy()
              next_arguments[i] = next
              Apply(head, next_arguments)
            })
          NoStep => ()
        }
        if i < last &&
          !root_failed &&
          rule(Apply(head, arguments[0:i + 1].to_owned())) is Some(_) {
          match root_step(term, rule_name, rule) {
            Reduced(_) as step => return step
            NoStep => root_failed = true
          }
        }
      }
      if root_failed {
        NoStep
      } else {
        root_step(term, rule_name, rule)
      }
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
    ApplicativeOrder => applicative_once(term, rule_name, rule)
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
