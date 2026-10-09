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

// Bounded-stack evaluation (issue #12).
//
// Evaluation is specified by three mutually recursive functions: `eval`
// (a term in an environment), `force` (a possibly delayed value) and `apply`
// (a function value to a delayed argument). Implemented as host recursion, a
// divergent term makes the host stack grow with the fuel spent, and the
// js/wasm stacks overflow long before a large budget runs out.
//
// The functions are run instead as one loop over an explicit continuation:
//
// - `EvalControl` is the next thing to do: `Evaluate` and `Force` are calls of
//   `eval` and `force`, `Return` hands a computed value to the continuation.
// - `EvalFrame` is a pending use of a value, the part of a caller that still
//   has to run when a call returns. The frames live in a heap `Array`.
//
// A call in tail position replaces the control and pushes nothing; a call
// whose result is still needed pushes the frame for the rest of the caller
// first. Steps happen in the order of the recursive definition and each one
// tests and spends fuel exactly where the recursive function did, so results
// and `consumed` are unchanged. Applying a closure to the last argument of a
// spine is a tail call, so a spinning redex such as Omega runs in a constant
// number of frames; a term that grows (`(λ. 0 0 0) (λ. 0 0 0)`) grows the
// frame array, which is bounded by the fuel and lives on the heap.

///|
/// The next step of the evaluation machine.
priv enum EvalControl[T] {
  /// Evaluate a term in an environment (index 0 first).
  Evaluate(@debruijn.DbTerm[T], Array[Semantic[T]])
  /// Force a value: evaluate it if it is delayed, return it otherwise.
  Force(Semantic[T])
  /// Pass a value in weak head form to the innermost frame.
  Return(Semantic[T])
}

///|
/// A pending step of the evaluation machine, waiting for a value.
priv enum EvalFrame[T] {
  /// Apply the returned value to `delay(arguments[next], environment)`, then
  /// the result to the remaining arguments of the spine.
  ApplyArguments(Array[@debruijn.DbTerm[T]], Int, Array[Semantic[T]])
  /// The returned value is a forced function: apply it to this argument.
  ApplyTo(Semantic[T])
}

///|
/// Runs the evaluation machine from `start` with `fuel` units. The host stack
/// depth is constant; pending work is kept in a heap array of frames.
fn[T] run_evaluation(start : EvalControl[T], fuel : Int) -> Run[T] {
  let frames : Array[EvalFrame[T]] = []
  for control = start, fuel = fuel {
    match control {
      Evaluate(term, environment) => {
        if fuel <= 0 {
          break Exhausted(0)
        }
        let remaining = fuel - 1
        match term {
          Value(value) => continue Return({ inner: Atom(value), }), remaining
          Free(name) =>
            continue Return({ inner: NeutralFree(name), }), remaining
          Bound(index) =>
            if index < 0 {
              break ScopeFailed(@debruijn.NegativeIndex(index~), remaining)
            } else if index >= environment.length() {
              break ScopeFailed(
                @debruijn.UnboundIndex(index~, depth=environment.length()),
                remaining,
              )
            } else {
              // eval(i, ρ) = force(ρ_i): a tail call
              continue Force(environment[index]), remaining
            }
          Bind(body) =>
            continue Return({ inner: Closure(body, environment), }), remaining
          Apply(head, arguments) => {
            // evaluate the head, then apply it to the delayed arguments in
            // order; an empty spine is the head itself
            if arguments.length() > 0 {
              frames.push(ApplyArguments(arguments, 0, environment))
            }
            continue Evaluate(head, environment), remaining
          }
        }
      }
      Force(value) => {
        if fuel <= 0 {
          break Exhausted(0)
        }
        match value.inner {
          Delayed(term, environment) =>
            continue Evaluate(term, environment), fuel - 1
          _ => continue Return(value), fuel - 1
        }
      }
      Return(value) =>
        match frames.pop() {
          None => break Done(value, fuel)
          Some(ApplyArguments(arguments, next, environment)) => {
            // apply(value, delay(u_next, ρ)) starts by forcing the function;
            // the frame for the remaining arguments goes below it, and none is
            // pushed after the last argument, so that application is a tail
            // call
            if next + 1 < arguments.length() {
              frames.push(ApplyArguments(arguments, next + 1, environment))
            }
            frames.push(
              ApplyTo({ inner: Delayed(arguments[next], environment), }),
            )
            continue Force(value), fuel
          }
          Some(ApplyTo(argument)) =>
            match value.inner {
              Closure(body, environment) => {
                // apply(clo(t, ρ), e) = eval(t, e · ρ): a tail call
                let next_environment = [argument]
                next_environment.append(environment)
                continue Evaluate(body, next_environment), fuel
              }
              _ =>
                continue Return({ inner: NeutralApply(value, argument), }), fuel
            }
        }
    }
  }
}

///|
/// Evaluates `term` in `environment` to weak head form.
fn[T] eval_semantic(
  term : @debruijn.DbTerm[T],
  environment : Array[Semantic[T]],
  fuel : Int,
) -> Run[T] {
  run_evaluation(Evaluate(term, environment), fuel)
}

///|
/// Forces `value` to weak head form.
fn[T] force(value : Semantic[T], fuel : Int) -> Run[T] {
  run_evaluation(Force(value), fuel)
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
  { inner: NeutralFree(name), }
}

///|
/// Reflects a quote level. Negative levels are rejected.
pub fn[T] reflect_level(level : Int) -> Semantic[T]? {
  if level < 0 {
    None
  } else {
    Some({ inner: NeutralLevel(level), })
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
/// The next step of the readback machine.
priv enum QuoteControl[T] {
  /// Read a value back under the given number of binders.
  ReadBack(Semantic[T], Int)
  /// Pass a read-back term to the innermost frame.
  Emit(@debruijn.DbTerm[T])
}

///|
/// A pending step of the readback machine, waiting for a term.
priv enum QuoteFrame[T] {
  /// The term is the body of a closure: wrap it in a binder.
  WrapBind
  /// The term is the head of a neutral application: read back this argument
  /// at this level next.
  QuoteArgument(Semantic[T], Int)
  /// The term is the argument of a neutral application with this head.
  WrapApply(@debruijn.DbTerm[T])
}

///|
/// Reads `value` back under `level` binders. Like `run_evaluation`, it keeps
/// pending work in a heap array of frames, because the read-back term can grow
/// with the fuel spent (for example the normal form `f (f (f ...))`).
fn[T] quote_semantic(
  value : Semantic[T],
  level : Int,
  fuel : Int,
) -> QuoteRun[T] {
  let frames : Array[QuoteFrame[T]] = []
  for control = ReadBack(value, level), fuel = fuel {
    match control {
      ReadBack(value, level) => {
        if fuel <= 0 {
          break QuoteExhausted(0)
        }
        match force(value, fuel - 1) {
          Exhausted(remaining) => break QuoteExhausted(remaining)
          ScopeFailed(error, remaining) =>
            break QuoteScopeFailed(error, remaining)
          Done(forced, remaining) =>
            match forced.inner {
              Atom(value) => continue Emit(Value(value)), remaining
              NeutralFree(name) => continue Emit(Free(name)), remaining
              NeutralLevel(variable_level) => {
                let index = level - variable_level - 1
                if index < 0 {
                  break QuoteScopeFailed(
                    @debruijn.NegativeIndex(index~),
                    remaining,
                  )
                }
                continue Emit(Bound(index)), remaining
              }
              Closure(body, environment) => {
                let next_environment : Array[Semantic[T]] = [
                  { inner: NeutralLevel(level), },
                ]
                next_environment.append(environment)
                match eval_semantic(body, next_environment, remaining) {
                  Exhausted(rest) => break QuoteExhausted(rest)
                  ScopeFailed(error, rest) =>
                    break QuoteScopeFailed(error, rest)
                  Done(body_value, rest) => {
                    frames.push(WrapBind)
                    continue ReadBack(body_value, level + 1), rest
                  }
                }
              }
              NeutralApply(function, argument) => {
                frames.push(QuoteArgument(argument, level))
                continue ReadBack(function, level), remaining
              }
              Delayed(_, _) =>
                abort("force must eliminate delayed semantic values")
            }
        }
      }
      Emit(term) =>
        match frames.pop() {
          None => break Quoted(term, fuel)
          Some(WrapBind) => continue Emit(Bind(term)), fuel
          Some(QuoteArgument(argument, argument_level)) => {
            frames.push(WrapApply(term))
            continue ReadBack(argument, argument_level), fuel
          }
          Some(WrapApply(function)) =>
            continue Emit(Apply(function, [term])), fuel
        }
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
