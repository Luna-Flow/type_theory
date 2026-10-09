///|
priv struct Closure {
  environment : Environment
  parameter : @core.Name
  body : TypedPlan
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
  // Lookup key, semantic value, source name to avoid during readback.
  // Internal capture-avoidance names must not perturb fresh output names.
  entries : Array[(@core.Name, Value, @core.Name)]
  length : Int
}

///|
fn Environment::extend_with(
  self : Environment,
  name : @core.Name,
  value : Value,
  source_name? : @core.Name = name,
) -> Environment {
  let entries = if self.entries.length() == self.length {
    self.entries
  } else {
    self.entries[0:self.length].to_owned()
  }
  entries.push((name, value, source_name))
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
    used = used.add(self.entries[i].2)
  }
  used
}

///|
/// Evaluation of an already elaborated plan; no source typing is repeated.
priv enum EvalControl {
  Evaluate(TypedPlan, Environment)
  ApplyValue(Value, Ty, Value)
  Return(Value)
}

///|
priv enum EvalFrame {
  PlanFunction(Ty, TypedPlan, Environment)
  PlanOperand(Value, Ty)
  PlanBinding(@core.Name, @core.Name, TypedPlan, Environment)
}

///|
fn run_evaluation(start : EvalControl) -> Result[Value, TypeError] {
  let frames : Array[EvalFrame] = []
  for control = start {
    match control {
      Evaluate(plan, environment) =>
        match plan {
          PlanValue(Atom::UnitLit, _) => continue Return(VUnit)
          PlanValue(Atom::Const(name), _) =>
            continue Return(VNeutral(NConst(name)))
          PlanVariable(name, _) =>
            match environment.lookup(name) {
              Some(value) => continue Return(value)
              None => break Err(TypeError::UnboundVariable(name))
            }
          PlanBind(parameter, _, body) =>
            continue Return(VLam({ environment, parameter, body, }))
          PlanApply(function, domain, argument, _) => {
            frames.push(PlanFunction(domain, argument, environment))
            continue Evaluate(function, environment)
          }
          PlanLet(parameter, original, argument, rest, _) => {
            frames.push(PlanBinding(parameter, original, rest, environment))
            continue Evaluate(argument, environment)
          }
        }
      ApplyValue(function, domain, argument) =>
        match function {
          VLam(closure) =>
            continue Evaluate(
                closure.body,
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
          Some(PlanFunction(domain, argument, environment)) => {
            frames.push(PlanOperand(value, domain))
            continue Evaluate(argument, environment)
          }
          Some(PlanOperand(function, domain)) =>
            continue ApplyValue(function, domain, value)
          Some(PlanBinding(parameter, original, rest, environment)) =>
            continue Evaluate(
                rest,
                environment.extend_with(parameter, value, source_name=original),
              )
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
  let entries : Array[(@core.Name, Value, @core.Name)] = []
  for entry in ctx.to_array() {
    entries.push((entry.0, reflect(entry.1, NFree(entry.0)), entry.0))
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
  let plan = match build_typed_plan(sig, CheckPlan(ctx, term, ty)) {
    Ok(plan) => plan
    Err(error) => return Err(error)
  }
  let used = @syntax.all_names(term).union(context_names(ctx))
  match run_evaluation(Evaluate(plan, initial_environment(ctx))) {
    Ok(value) => reify(ty, value, used)
    Err(error) => Err(error)
  }
}
