///|
priv struct Closure {
  environment : Array[(@core.Name, Value)]
  parameter : @core.Name
  body : Term
}

///|
priv enum Neutral {
  NFree(@core.Name)
  NApp(Neutral, Value)
}

///|
priv enum Value {
  VUnit
  VAtom(Atom)
  VLam(Closure)
  VNeutral(Neutral)
}

///|
fn env_lookup(
  environment : Array[(@core.Name, Value)],
  name : @core.Name,
) -> Value? {
  for i = environment.length() - 1; i >= 0; i = i - 1 {
    if environment[i].0 == name {
      return Some(environment[i].1)
    }
  }
  None
}

///|
fn quote_neutral(neutral : Neutral) -> Result[Term, TypeError] {
  match neutral {
    NFree(name) => Ok(@syntax.Variable(name))
    NApp(function, argument) =>
      match quote_neutral(function) {
        Err(error) => Err(error)
        Ok(quoted_function) =>
          match quote_untyped(argument) {
            Err(error) => Err(error)
            Ok(quoted_argument) =>
              Ok(@syntax.Apply(quoted_function, [quoted_argument]))
          }
      }
  }
}

///|
fn quote_untyped(value : Value) -> Result[Term, TypeError] {
  match value {
    VUnit => Ok(@syntax.Value(Atom::UnitLit))
    VAtom(atom) => Ok(@syntax.Value(atom))
    VNeutral(neutral) => quote_neutral(neutral)
    VLam(_) =>
      Err(
        TypeError::NormalizationError(
          message="cannot quote function without a type",
        ),
      )
  }
}

///|
fn apply_value(function : Value, argument : Value) -> Result[Value, TypeError] {
  match function {
    VLam(closure) => {
      let next_environment = closure.environment.copy()
      next_environment.push((closure.parameter, argument))
      eval(closure.body, next_environment)
    }
    VNeutral(neutral) => Ok(VNeutral(NApp(neutral, argument)))
    _ =>
      Err(
        TypeError::NormalizationError(
          message="attempted to apply a non-functional semantic value",
        ),
      )
  }
}

///|
fn eval(
  term : Term,
  environment : Array[(@core.Name, Value)],
) -> Result[Value, TypeError] {
  match term {
    @syntax.Value(Atom::UnitLit) => Ok(VUnit)
    @syntax.Value(atom) => Ok(VAtom(atom))
    @syntax.Variable(name) =>
      match env_lookup(environment, name) {
        Some(value) => Ok(value)
        None => Err(TypeError::UnboundVariable(name))
      }
    @syntax.Bind(parameter, body) => Ok(VLam({ environment, parameter, body }))
    @syntax.Apply(head, arguments) => {
      if arguments.length() == 0 {
        return Err(TypeError::EmptyApplication)
      }
      let mut current = match eval(head, environment) {
        Ok(value) => value
        Err(error) => return Err(error)
      }
      for argument in arguments {
        let argument_value = match eval(argument, environment) {
          Ok(value) => value
          Err(error) => return Err(error)
        }
        match apply_value(current, argument_value) {
          Ok(next) => current = next
          Err(error) => return Err(error)
        }
      }
      Ok(current)
    }
  }
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
fn reify_with_name(
  ty : Ty,
  value : Value,
  fresh : @core.Name,
) -> Result[Term, TypeError] {
  match ty {
    Ty::Base(_) =>
      match value {
        VAtom(atom) => Ok(@syntax.Value(atom))
        VNeutral(neutral) => quote_neutral(neutral)
        VUnit =>
          Err(
            TypeError::NormalizationError(
              message="unit semantic value cannot inhabit a base type",
            ),
          )
        VLam(_) =>
          Err(
            TypeError::NormalizationError(
              message="function semantic value cannot inhabit a base type",
            ),
          )
      }
    Ty::Unit =>
      match value {
        VUnit => Ok(@syntax.Value(Atom::UnitLit))
        VNeutral(neutral) => quote_neutral(neutral)
        VAtom(Atom::UnitLit) => Ok(@syntax.Value(Atom::UnitLit))
        VAtom(Atom::Const(_)) =>
          Err(
            TypeError::NormalizationError(
              message="constant atom cannot inhabit unit without reduction",
            ),
          )
        VLam(_) =>
          Err(
            TypeError::NormalizationError(
              message="function semantic value cannot inhabit unit type",
            ),
          )
      }
    Ty::Arrow(domain, codomain) => {
      let argument = reflect(domain, NFree(fresh))
      match apply_value(value, argument) {
        Ok(body_value) =>
          match reify(codomain, body_value, @hashset.from_array([fresh])) {
            Ok(body) => Ok(@syntax.Bind(fresh, body))
            Err(error) => Err(error)
          }
        Err(error) => Err(error)
      }
    }
  }
}

///|
fn collect_environment_names(
  environment : Array[(@core.Name, Value)],
) -> @hashset.HashSet[@core.Name] {
  let mut used = @hashset.new()
  for entry in environment {
    used = used.add(entry.0)
  }
  used
}

///|
fn reify_with_used(
  ty : Ty,
  value : Value,
  used : @hashset.HashSet[@core.Name],
) -> Result[Term, TypeError] {
  match ty {
    Ty::Arrow(domain, codomain) => {
      let fresh = @core.fresh_name(@core.Name::new("x"), used)
      let argument = reflect(domain, NFree(fresh))
      match apply_value(value, argument) {
        Ok(body_value) =>
          match reify_with_used(codomain, body_value, used.add(fresh)) {
            Ok(body) => Ok(@syntax.Bind(fresh, body))
            Err(error) => Err(error)
          }
        Err(error) => Err(error)
      }
    }
    _ => reify_with_name(ty, value, @core.Name::new("x"))
  }
}

///|
fn reify(
  ty : Ty,
  value : Value,
  used : @hashset.HashSet[@core.Name],
) -> Result[Term, TypeError] {
  let value_used = match value {
    VLam(closure) => used.union(collect_environment_names(closure.environment))
    _ => used
  }
  reify_with_used(ty, value, value_used)
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
fn initial_environment(ctx : TypeContext) -> Array[(@core.Name, Value)] {
  let environment : Array[(@core.Name, Value)] = []
  for entry in ctx.to_array() {
    environment.push((entry.0, reflect(entry.1, NFree(entry.0))))
  }
  environment
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
  let _ = sig
  let used = @syntax.all_names(term).union(context_names(ctx))
  match eval(term, initial_environment(ctx)) {
    Ok(value) => reify(ty, value, used)
    Err(error) => Err(error)
  }
}
