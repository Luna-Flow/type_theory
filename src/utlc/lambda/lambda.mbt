///|
/// Constructs a lambda abstraction using the shared binding syntax.
pub fn[T] abstraction(
  parameter : @core.Name,
  body : @syntax.Term[T],
) -> @syntax.Term[T] {
  Bind(parameter, body)
}

///|
/// Constructs unary application using the generic application node.
pub fn[T] application(
  function : @syntax.Term[T],
  argument : @syntax.Term[T],
) -> @syntax.Term[T] {
  Apply(function, [argument])
}

///|
/// Removes empty applications `Apply(h, [])` around a term.
///
/// An application with no arguments is read as its head, so it never hides a
/// redex or an eta-reducible argument.
fn[T] strip_empty_applications(term : @syntax.Term[T]) -> @syntax.Term[T] {
  match term {
    Apply(head, []) => strip_empty_applications(head)
    _ => term
  }
}

///|
/// One beta rule, independent of the domain value type.
///
/// Empty applications in the head are read as their head, so
/// `Apply(Apply(Bind(x, b), []), [a])` is a redex.
pub fn[T] beta_rule(term : @syntax.Term[T]) -> @syntax.Term[T]? {
  match term {
    Apply(head, arguments) if arguments.length() > 0 =>
      match strip_empty_applications(head) {
        Bind(parameter, body) => {
          let reduced = @substitution.Substitution::singleton(
            parameter,
            arguments[0],
          ).apply(body)
          if arguments.length() == 1 {
            Some(reduced)
          } else {
            Some(Apply(reduced, arguments[1:].to_owned()))
          }
        }
        _ => None
      }
    _ => None
  }
}

///|
/// One eta rule. The bound variable must not occur free in the function.
///
/// Empty applications are read as their head, both around the body and around
/// the argument.
pub fn[T] eta_rule(term : @syntax.Term[T]) -> @syntax.Term[T]? {
  match term {
    Bind(parameter, body) =>
      match strip_empty_applications(body) {
        Apply(function, [argument]) =>
          match strip_empty_applications(argument) {
            Variable(name) =>
              if name == parameter &&
                !@syntax.free_variables(function).contains(parameter) {
                Some(function)
              } else {
                None
              }
            _ => None
          }
        _ => None
      }
    _ => None
  }
}

///|
/// Tries beta reduction before eta reduction.
pub fn[T] beta_eta_rule(term : @syntax.Term[T]) -> @syntax.Term[T]? {
  match beta_rule(term) {
    Some(result) => Some(result)
    None => eta_rule(term)
  }
}

///|
/// Normalizes a lambda term using the shared evaluator.
pub fn[T] normalize(
  term : @syntax.Term[T],
  max_steps : Int,
) -> @rewrite.NormalizationResult[T] {
  @eval.evaluate(
    term,
    @rewrite.RuleName::unsafe_new("beta_eta"),
    beta_eta_rule,
    NormalOrder,
    max_steps,
  )
}
