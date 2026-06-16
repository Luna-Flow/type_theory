///|
/// Opaque semantic value produced by bounded evaluation.
pub struct Semantic[T] {
  inner : SemanticInner[T]
}

///|
/// Lazy semantic domain for untyped normalization by evaluation.
enum SemanticInner[T] {
  Atom(T)
  Closure(@debruijn.DbTerm[T], Array[Semantic[T]])
  Delayed(@debruijn.DbTerm[T], Array[Semantic[T]])
  NeutralFree(@core.Name)
  NeutralLevel(Int)
  NeutralApply(Semantic[T], Semantic[T])
}

///|
/// Public bounded semantic evaluation result.
pub(all) enum EvaluationResult[T] {
  Evaluated(value~ : Semantic[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
}

///|
/// Public bounded quote/readback result.
pub(all) enum QuoteResult[T] {
  Quoted(term~ : @debruijn.DbTerm[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
}

///|
/// Observable result of bounded untyped NbE.
pub(all) enum NbeResult[T] {
  NormalForm(term~ : @debruijn.DbTerm[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
} derive(Eq, Debug)

///|
priv enum Run[T] {
  Done(Semantic[T], Int)
  Exhausted(Int)
  ScopeFailed(@debruijn.ScopeError, Int)
}

///|
fn consumed(initial : Int, remaining : Int) -> Int {
  initial - remaining
}

///|
fn[T] force(value : Semantic[T], fuel : Int) -> Run[T] {
  if fuel <= 0 {
    return Exhausted(0)
  }
  match value.inner {
    Delayed(term, environment) => eval_semantic(term, environment, fuel - 1)
    _ => Done(value, fuel - 1)
  }
}

///|
fn[T] apply_semantic(
  function : Semantic[T],
  argument : Semantic[T],
  fuel : Int,
) -> Run[T] {
  match force(function, fuel) {
    Exhausted(remaining) => Exhausted(remaining)
    ScopeFailed(error, remaining) => ScopeFailed(error, remaining)
    Done(forced, remaining) =>
      match forced.inner {
        Closure(body, environment) => {
          let next_environment = [argument]
          next_environment.append(environment)
          eval_semantic(body, next_environment, remaining)
        }
        _ => Done({ inner: NeutralApply(forced, argument) }, remaining)
      }
  }
}

///|
fn[T] eval_semantic(
  term : @debruijn.DbTerm[T],
  environment : Array[Semantic[T]],
  fuel : Int,
) -> Run[T] {
  if fuel <= 0 {
    return Exhausted(0)
  }
  let remaining = fuel - 1
  match term {
    Value(value) => Done({ inner: Atom(value) }, remaining)
    Free(name) => Done({ inner: NeutralFree(name) }, remaining)
    Bound(index) =>
      if index < 0 {
        ScopeFailed(@debruijn.NegativeIndex(index~), remaining)
      } else if index >= environment.length() {
        ScopeFailed(
          @debruijn.UnboundIndex(index~, depth=environment.length()),
          remaining,
        )
      } else {
        force(environment[index], remaining)
      }
    Bind(body) => Done({ inner: Closure(body, environment) }, remaining)
    Apply(head, arguments) =>
      match eval_semantic(head, environment, remaining) {
        Exhausted(rest) => Exhausted(rest)
        ScopeFailed(error, rest) => ScopeFailed(error, rest)
        Done(head_value, rest) => {
          let mut current = head_value
          let mut current_fuel = rest
          for argument in arguments {
            let delayed : Semantic[T] = {
              inner: Delayed(argument, environment),
            }
            match apply_semantic(current, delayed, current_fuel) {
              Exhausted(next_fuel) => return Exhausted(next_fuel)
              ScopeFailed(error, next_fuel) =>
                return ScopeFailed(error, next_fuel)
              Done(next, next_fuel) => {
                current = next
                current_fuel = next_fuel
              }
            }
          }
          Done(current, current_fuel)
        }
      }
  }
}

///|
priv enum QuoteRun[T] {
  Quoted(@debruijn.DbTerm[T], Int)
  QuoteExhausted(Int)
  QuoteScopeFailed(@debruijn.ScopeError, Int)
}

///|
/// Reflects a named free variable into the neutral semantic domain.
pub fn[T] reflect_free(name : @core.Name) -> Semantic[T] {
  { inner: NeutralFree(name) }
}

///|
/// Reflects a quote level. Negative levels are rejected.
pub fn[T] reflect_level(level : Int) -> Semantic[T]? {
  if level < 0 {
    None
  } else {
    Some({ inner: NeutralLevel(level) })
  }
}

///|
/// Evaluates a closed De Bruijn term into the lazy semantic domain.
pub fn[T] eval(term : @debruijn.DbTerm[T], fuel : Int) -> EvaluationResult[T] {
  if fuel <= 0 {
    return EvaluationResult::FuelExhausted(consumed=0)
  }
  match @debruijn.validate(term) {
    Err(error) => EvaluationResult::ScopeFailure(error~, consumed=0)
    Ok(_) =>
      match eval_semantic(term, [], fuel) {
        Done(value, remaining) =>
          Evaluated(value~, consumed=consumed(fuel, remaining))
        Exhausted(remaining) =>
          EvaluationResult::FuelExhausted(consumed=consumed(fuel, remaining))
        ScopeFailed(error, remaining) =>
          EvaluationResult::ScopeFailure(
            error~,
            consumed=consumed(fuel, remaining),
          )
      }
  }
}

///|
/// Quotes a semantic value to beta-normal De Bruijn syntax.
pub fn[T] quote(value : Semantic[T], level : Int, fuel : Int) -> QuoteResult[T] {
  if level < 0 {
    return QuoteResult::ScopeFailure(
      error=@debruijn.NegativeIndex(index=level),
      consumed=0,
    )
  }
  if fuel <= 0 {
    return QuoteResult::FuelExhausted(consumed=0)
  }
  match quote_semantic(value, level, fuel) {
    Quoted(term, remaining) =>
      QuoteResult::Quoted(term~, consumed=consumed(fuel, remaining))
    QuoteExhausted(remaining) =>
      QuoteResult::FuelExhausted(consumed=consumed(fuel, remaining))
    QuoteScopeFailed(error, remaining) =>
      QuoteResult::ScopeFailure(error~, consumed=consumed(fuel, remaining))
  }
}

///|
fn[T] quote_semantic(
  value : Semantic[T],
  level : Int,
  fuel : Int,
) -> QuoteRun[T] {
  if fuel <= 0 {
    return QuoteExhausted(0)
  }
  match force(value, fuel - 1) {
    Exhausted(remaining) => QuoteExhausted(remaining)
    ScopeFailed(error, remaining) => QuoteScopeFailed(error, remaining)
    Done(forced, remaining) =>
      match forced.inner {
        Atom(value) => Quoted(Value(value), remaining)
        NeutralFree(name) => Quoted(Free(name), remaining)
        NeutralLevel(variable_level) => {
          let index = level - variable_level - 1
          if index < 0 {
            QuoteScopeFailed(@debruijn.NegativeIndex(index~), remaining)
          } else {
            Quoted(Bound(index), remaining)
          }
        }
        Closure(body, environment) => {
          let next_environment : Array[Semantic[T]] = [
            { inner: NeutralLevel(level) },
          ]
          next_environment.append(environment)
          match eval_semantic(body, next_environment, remaining) {
            Exhausted(rest) => QuoteExhausted(rest)
            ScopeFailed(error, rest) => QuoteScopeFailed(error, rest)
            Done(body_value, rest) =>
              match quote_semantic(body_value, level + 1, rest) {
                Quoted(quoted_body, final_fuel) =>
                  Quoted(Bind(quoted_body), final_fuel)
                QuoteExhausted(final_fuel) => QuoteExhausted(final_fuel)
                QuoteScopeFailed(error, final_fuel) =>
                  QuoteScopeFailed(error, final_fuel)
              }
          }
        }
        NeutralApply(function, argument) =>
          match quote_semantic(function, level, remaining) {
            QuoteExhausted(rest) => QuoteExhausted(rest)
            QuoteScopeFailed(error, rest) => QuoteScopeFailed(error, rest)
            Quoted(quoted_function, rest) =>
              match quote_semantic(argument, level, rest) {
                Quoted(quoted_argument, final_fuel) =>
                  Quoted(Apply(quoted_function, [quoted_argument]), final_fuel)
                QuoteExhausted(final_fuel) => QuoteExhausted(final_fuel)
                QuoteScopeFailed(error, final_fuel) =>
                  QuoteScopeFailed(error, final_fuel)
              }
          }
        Delayed(_, _) => abort("force must eliminate delayed semantic values")
      }
  }
}

///|
/// Bounded beta normalization by evaluation for untyped De Bruijn terms.
pub fn[T] normalize(term : @debruijn.DbTerm[T], fuel : Int) -> NbeResult[T] {
  if fuel <= 0 {
    return FuelExhausted(consumed=0)
  }
  match @debruijn.validate(term) {
    Err(error) => ScopeFailure(error~, consumed=0)
    Ok(_) =>
      match eval_semantic(term, [], fuel) {
        Exhausted(remaining) =>
          FuelExhausted(consumed=consumed(fuel, remaining))
        ScopeFailed(error, remaining) =>
          ScopeFailure(error~, consumed=consumed(fuel, remaining))
        Done(value, remaining) =>
          match quote_semantic(value, 0, remaining) {
            Quoted(normal, final_fuel) =>
              NormalForm(term=normal, consumed=consumed(fuel, final_fuel))
            QuoteExhausted(final_fuel) =>
              FuelExhausted(consumed=consumed(fuel, final_fuel))
            QuoteScopeFailed(error, final_fuel) =>
              ScopeFailure(error~, consumed=consumed(fuel, final_fuel))
          }
      }
  }
}
