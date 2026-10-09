///|
priv struct Closure {
  sig : Signature
  ctx : TypeContext
  environment : Environment
  parameter : @core.Name
  domain : Ty
  codomain : Ty
  body : Term
}

///|
priv enum Neutral {
  NFree(@core.Name)
  NConst(@core.Name)
  NApp(Neutral, Ty, Value)
}

///|
priv enum Value {
  VUnit
  VLam(Closure)
  VNeutral(Neutral)
}

///|
/// An evaluation environment: the values of the variables in scope, in binding
/// order. A later entry shadows an earlier one.
///
/// Like `TypeContext`, environments extended from one another share their
/// array (issue #13): `extend_with` pushes onto it when `self` is the longest
/// environment stored there and copies the prefix otherwise, and an
/// environment only reads its first `length` entries. Entering `n` nested
/// closures therefore takes amortized `O(n)` time instead of `O(n^2)`.
priv struct Environment {
  entries : Array[(@core.Name, Value)]
  length : Int
}

///|
fn Environment::extend_with(
  self : Environment,
  name : @core.Name,
  value : Value,
) -> Environment {
  let entries = if self.entries.length() == self.length {
    self.entries
  } else {
    self.entries[0:self.length].to_owned()
  }
  entries.push((name, value))
  { entries, length: self.length + 1, }
}

///|
fn Environment::lookup(self : Environment, name : @core.Name) -> Value? {
  for i = self.length - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
fn Environment::names(self : Environment) -> @hashset.HashSet[@core.Name] {
  let mut used = @hashset.new()
  for i in 0..<self.length {
    used = used.add(self.entries[i].0)
  }
  used
}

///|
/// Removes the first `count` domains from a function type: the type of a head
/// of type `ty` once it has been applied to `count` arguments.
fn drop_domains(ty : Ty, count : Int) -> Result[Ty, TypeError] {
  let mut current = ty
  for _ in 0..<count {
    match current {
      Ty::Arrow(_, codomain) => current = codomain
      _ => return Err(TypeError::ExpectedFunction(current))
    }
  }
  Ok(current)
}

///|
/// Computes the type at which `head` must be evaluated so that the flattened
/// application `head arguments` has type `expected`.
///
/// A lambda head cannot be inferred, so its type is rebuilt from the redex
/// rule: the first argument gives the domain, and the codomain is the type of
/// the remaining spine `b a2 ... an`, computed by the same `redex_step` that
/// `infer` and `check` use. A body that is itself an application joins that
/// spine, and its own arguments are dropped from the result to obtain the type
/// of the body. When the spine runs out of arguments the body is in checking
/// position and its type is `expected`, as in the checking-mode redex rule
/// (issue #8); this covers a body that is a lambda, which cannot be inferred.
/// Any other head is inferred.
///
/// The definition expands each lambda redex, infers its first argument, and
/// recurses on the body joined with the trailing arguments; it builds the type
/// while returning. It is run as two loops (issue #13): the first takes redex
/// steps down the spine and keeps them in a heap array, the second builds the
/// type from the innermost step outwards. Errors are met in the same order.
fn head_type_for_application(
  sig : Signature,
  ctx : TypeContext,
  head : Term,
  arguments : Array[Term],
  expected : Ty,
) -> Result[Ty, TypeError] {
  if arguments.length() == 0 {
    return Err(TypeError::EmptyApplication)
  }
  // the redex steps whose remaining spine is not empty, outermost first
  let steps : Array[RedexStep] = []
  // the type computed for the innermost spine
  let mut result = for ctx = ctx, head = head, arguments = arguments {
    match head {
      @syntax.Bind(parameter, body) => {
        let step = match redex_step(sig, ctx, parameter, body, arguments) {
          Ok(step) => step
          Err(error) => return Err(error)
        }
        if step.arguments.length() == 0 {
          break Ty::Arrow(step.domain, expected)
        }
        steps.push(step)
        continue step.ctx, step.head, step.arguments
      }
      _ =>
        match infer(sig, ctx, head) {
          Ok(head_type) => break head_type
          Err(error) => return Err(error)
        }
    }
  }
  for i = steps.length() - 1; i >= 0; i = i - 1 {
    let body_type = match drop_domains(result, steps[i].body_arity) {
      Ok(body_type) => body_type
      Err(error) => return Err(error)
    }
    result = Ty::Arrow(steps[i].domain, body_type)
  }
  Ok(result)
}

// Bounded-stack typed evaluation and readback (issue #13).
//
// Typed evaluation is specified by two mutually recursive functions:
// `eval_typed`, which evaluates a term at a type, and `apply_value_typed`,
// which applies a semantic function to an argument and evaluates the body of a
// closure. Readback is specified by `reify` (a value at a type, eta-expanding
// at arrow types) and `quote_neutral` (a neutral, reifying the arguments of
// its spine). Implemented as host recursion, the depth of the host stack grows
// with the nesting depth of the term, of the types and of the normal form, and
// the js and wasm stacks overflow at a depth of a few thousand.
//
// Both are run instead as loops over an explicit continuation, like the
// untyped evaluator of `utlc/nbe` (issue #12) and the type checker of this
// package: a control says what to do next, and the frames, the rest of the
// callers, live in a heap `Array`. A call in tail position pushes nothing.
// Every step happens in the order of the recursive definition, and an error is
// never caught and replaced, so results and errors are unchanged.

///|
/// The next step of the typed evaluation machine.
priv enum EvalControl {
  /// `eval_typed(sig, ctx, term, ty, environment)`.
  Evaluate(Signature, TypeContext, Term, Ty, Environment)
  /// `apply_value_typed(function, domain, argument)`.
  ApplyValue(Value, Ty, Value)
  /// Pass a value to the innermost frame.
  Return(Value)
}

///|
/// A pending step of the typed evaluation machine, waiting for a value.
priv enum EvalFrame {
  /// The value is the application of a spine head to the arguments before
  /// `next`, of type `current_type`: apply it to the remaining arguments.
  Spine(Signature, TypeContext, Array[Term], Environment, Int, Ty)
  /// The value is argument `index` of a spine, of type `domain`: apply
  /// `function`, the application before it, to it.
  Argument(Signature, TypeContext, Array[Term], Environment, Int, Value, Ty, Ty)
}

///|
/// Continues a spine whose application before argument `next` has value
/// `function` and type `current_type`. Returns the next control after pushing
/// the frame that waits for the value of the argument.
fn continue_spine(
  frames : Array[EvalFrame],
  sig : Signature,
  ctx : TypeContext,
  arguments : Array[Term],
  environment : Environment,
  next : Int,
  function : Value,
  current_type : Ty,
) -> Result[EvalControl, TypeError] {
  if next == arguments.length() {
    return Ok(Return(function))
  }
  match current_type {
    Ty::Arrow(domain, codomain) => {
      // `normalize_eta_long` checks the complete source term before evaluation.
      // Lambda bodies and every argument are subterms covered by that check,
      // so checking an argument again here repeats work that its own evaluation
      // will also repeat for any nested application. The environment invariant
      // established by the checker supplies the same `domain` here.
      frames.push(
        Argument(
          sig, ctx, arguments, environment, next, function, domain, codomain,
        ),
      )
      Ok(Evaluate(sig, ctx, arguments[next], domain, environment))
    }
    _ => Err(TypeError::ExpectedFunction(current_type))
  }
}

///|
/// Runs the typed evaluation machine from `start`. The host stack depth is
/// constant; pending work is kept in a heap array of frames.
fn run_evaluation(start : EvalControl) -> Result[Value, TypeError] {
  let frames : Array[EvalFrame] = []
  for control = start {
    match control {
      Evaluate(sig, ctx, term, ty, environment) =>
        match term {
          @syntax.Value(Atom::UnitLit) => continue Return(VUnit)
          @syntax.Value(Atom::Const(name)) =>
            continue Return(VNeutral(NConst(name)))
          @syntax.Variable(name) =>
            match environment.lookup(name) {
              Some(value) => continue Return(value)
              None => break Err(TypeError::UnboundVariable(name))
            }
          @syntax.Bind(parameter, body) =>
            match ty {
              Ty::Arrow(domain, codomain) =>
                continue Return(
                    VLam({
                      sig,
                      ctx,
                      environment,
                      parameter,
                      domain,
                      codomain,
                      body,
                    }),
                  )
              _ =>
                break Err(
                  TypeError::NormalizationError(
                    message="lambda semantic value requires an arrow type",
                  ),
                )
            }
          @syntax.Apply(_, _) => {
            let (head, arguments) = match application_spine(term) {
              Ok(spine) => spine
              Err(error) => break Err(error)
            }
            let head_type = match
              head_type_for_application(sig, ctx, head, arguments, ty) {
              Ok(head_type) => head_type
              Err(error) => break Err(error)
            }
            // evaluate the head, then apply it to the arguments in order
            frames.push(Spine(sig, ctx, arguments, environment, 0, head_type))
            continue Evaluate(sig, ctx, head, head_type, environment)
          }
        }
      ApplyValue(function, domain, argument) =>
        match function {
          VLam(closure) =>
            // apply(clo, a) = eval_typed(body, environment · a): a tail call
            continue Evaluate(
                closure.sig,
                closure.ctx.extend_with(closure.parameter, closure.domain),
                closure.body,
                closure.codomain,
                closure.environment.extend_with(closure.parameter, argument),
              )
          VNeutral(neutral) =>
            continue Return(VNeutral(NApp(neutral, domain, argument)))
          _ =>
            break Err(
              TypeError::NormalizationError(
                message="attempted to apply a non-functional semantic value",
              ),
            )
        }
      Return(value) =>
        match frames.pop() {
          None => break Ok(value)
          Some(Spine(sig, ctx, arguments, environment, next, current_type)) =>
            match
              continue_spine(
                frames, sig, ctx, arguments, environment, next, value, current_type,
              ) {
              Ok(next_control) => continue next_control
              Err(error) => break Err(error)
            }
          Some(
            Argument(
              sig,
              ctx,
              arguments,
              environment,
              index,
              function,
              domain,
              codomain
            )
          ) => {
            // the application to this argument is the value of the spine
            // before the next one; after the last argument it is the value of
            // the whole spine, and the application is a tail call
            if index + 1 < arguments.length() {
              frames.push(
                Spine(sig, ctx, arguments, environment, index + 1, codomain),
              )
            }
            continue ApplyValue(function, domain, value)
          }
        }
    }
  }
}

///|
fn apply_value_typed(
  function : Value,
  domain : Ty,
  argument : Value,
) -> Result[Value, TypeError] {
  run_evaluation(ApplyValue(function, domain, argument))
}

///|
fn eval_typed(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  ty : Ty,
  environment : Environment,
) -> Result[Value, TypeError] {
  run_evaluation(Evaluate(sig, ctx, term, ty, environment))
}

///|
fn reflect(ty : Ty, neutral : Neutral) -> Value {
  match ty {
    Ty::Arrow(_, _) => VNeutral(neutral)
    Ty::Base(_) => VNeutral(neutral)
    Ty::Unit => VNeutral(neutral)
  }
}

///|
/// The names a readback must avoid, with a lower bound on the binder names
/// already taken.
///
/// Readback names binders with `@core.fresh_name(x, used)`, which tries the
/// candidates `x`, `x_1`, `x_2`, ... in order and returns the first one not in
/// `used`. Eta-expanding at a type with `n` arrows, or at a type nested `n`
/// levels deep in its domains, chooses `n` names, each fresh for the names
/// chosen before it on the path; tried from the start, each choice would
/// retry every candidate chosen before, `O(n^2)` lookups in all (issue #13).
///
/// `skip` is a position before which every candidate is known to be in
/// `names`, so `fresh` starts there and returns the same name as
/// `@core.fresh_name`. The bound stays true as `names` grows: `fresh` returns
/// the candidate at some position `p >= skip` and adds it, so every candidate
/// before `p + 1` is in the new set, and `union` only adds names.
priv struct Used {
  names : @hashset.HashSet[@core.Name]
  skip : Int
}

///|
/// The first candidate based on `hint` not in `self.names`, and `self` with it
/// added.
fn Used::fresh(self : Used, hint : @core.Name) -> (@core.Name, Used) {
  for position = self.skip; ; position = position + 1 {
    let candidate = if position == 0 {
      hint
    } else {
      @core.Name::new(hint.text() + "_" + position.to_string())
    }
    if !self.names.contains(candidate) {
      return (
        candidate,
        { names: self.names.add(candidate), skip: position + 1, },
      )
    }
  }
}

///|
/// The next step of the readback machine.
priv enum ReadControl {
  /// `reify(ty, value, used)`: add the names bound in the environment of a
  /// closure to `used`, then `reify_with_used`.
  Reify(Ty, Value, Used)
  /// `reify_with_used(ty, value, used)`: eta-expand at an arrow type, read
  /// back a value of a base or unit type.
  ReifyWithUsed(Ty, Value, Used)
  /// `quote_neutral(neutral, used)`.
  Quote(Neutral, Used)
  /// Pass a read-back term to the innermost frame.
  Emit(Term)
}

///|
/// A pending step of the readback machine, waiting for a term.
priv enum ReadFrame {
  /// The term is the body of an eta-expansion: wrap it in this binder.
  WrapBind(@core.Name)
  /// The term is the function of a neutral application: read back its
  /// argument, of type `domain`, next.
  ReifyArgument(Ty, Value, Used)
  /// The term is the argument of a neutral application with this function.
  WrapApply(Term)
}

///|
/// Reads `value` back at type `ty`, in beta-normal eta-long form, with binder
/// names fresh for `used`. The host stack depth is constant; pending work is
/// kept in a heap array of frames.
fn reify(
  ty : Ty,
  value : Value,
  used : @hashset.HashSet[@core.Name],
) -> Result[Term, TypeError] {
  let frames : Array[ReadFrame] = []
  let hint = @core.Name::new("x")
  for control = Reify(ty, value, { names: used, skip: 0, }) {
    match control {
      Reify(ty, value, used) => {
        let value_used = match value {
          VLam(closure) =>
            { ..used, names: used.names.union(closure.environment.names()), }
          _ => used
        }
        continue ReifyWithUsed(ty, value, value_used)
      }
      ReifyWithUsed(Ty::Arrow(domain, codomain), value, used) => {
        let (fresh, body_used) = used.fresh(hint)
        let argument = reflect(domain, NFree(fresh))
        match apply_value_typed(value, domain, argument) {
          Ok(body_value) => {
            frames.push(WrapBind(fresh))
            continue ReifyWithUsed(codomain, body_value, body_used)
          }
          Err(error) => break Err(error)
        }
      }
      ReifyWithUsed(Ty::Base(_), value, used) =>
        match value {
          VNeutral(neutral) => continue Quote(neutral, used)
          VUnit =>
            break Err(
              TypeError::NormalizationError(
                message="unit semantic value cannot inhabit a base type",
              ),
            )
          VLam(_) =>
            break Err(
              TypeError::NormalizationError(
                message="function semantic value cannot inhabit a base type",
              ),
            )
        }
      ReifyWithUsed(Ty::Unit, value, used) =>
        match value {
          VUnit => continue Emit(@syntax.Value(Atom::UnitLit))
          VNeutral(neutral) => continue Quote(neutral, used)
          VLam(_) =>
            break Err(
              TypeError::NormalizationError(
                message="function semantic value cannot inhabit unit type",
              ),
            )
        }
      Quote(NFree(name), _) => continue Emit(@syntax.Variable(name))
      Quote(NConst(name), _) => continue Emit(@syntax.Value(Atom::Const(name)))
      Quote(NApp(function, domain, argument), used) => {
        // the function first, then the argument
        frames.push(ReifyArgument(domain, argument, used))
        continue Quote(function, used)
      }
      Emit(term) =>
        match frames.pop() {
          None => break Ok(term)
          Some(WrapBind(name)) => continue Emit(@syntax.Bind(name, term))
          Some(ReifyArgument(domain, argument, used)) => {
            frames.push(WrapApply(term))
            continue Reify(domain, argument, used)
          }
          Some(WrapApply(function)) =>
            continue Emit(@syntax.Apply(function, [term]))
        }
    }
  }
}

///|
fn context_names(ctx : TypeContext) -> @hashset.HashSet[@core.Name] {
  let mut used = @hashset.new()
  for entry in ctx.to_array() {
    used = used.add(entry.0)
  }
  used
}

///|
fn initial_environment(ctx : TypeContext) -> Environment {
  let entries : Array[(@core.Name, Value)] = []
  for entry in ctx.to_array() {
    entries.push((entry.0, reflect(entry.1, NFree(entry.0))))
  }
  { entries, length: entries.length(), }
}

///|
pub fn normalize_eta_long(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  ty : Ty,
) -> Result[Term, TypeError] {
  match check(sig, ctx, term, ty) {
    Ok(_) => ()
    Err(error) => return Err(error)
  }
  let used = @syntax.all_names(term).union(context_names(ctx))
  match eval_typed(sig, ctx, term, ty, initial_environment(ctx)) {
    Ok(value) => reify(ty, value, used)
    Err(error) => Err(error)
  }
}
