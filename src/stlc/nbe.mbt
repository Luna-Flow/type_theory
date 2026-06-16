///|
priv struct Closure {
  sig : Signature
  ctx : TypeContext
  environment : Array[(@core.Name, Value)]
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
fn quote_neutral(
  neutral : Neutral,
  used : @hashset.HashSet[@core.Name],
) -> Result[Term, TypeError] {
  match neutral {
    NFree(name) => Ok(@syntax.Variable(name))
    NConst(name) => Ok(@syntax.Value(Atom::Const(name)))
    NApp(function, domain, argument) =>
      match quote_neutral(function, used) {
        Err(error) => Err(error)
        Ok(quoted_function) =>
          match reify(domain, argument, used) {
            Err(error) => Err(error)
            Ok(quoted_argument) =>
              Ok(@syntax.Apply(quoted_function, [quoted_argument]))
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
  match function {
    VLam(closure) => {
      let next_environment = closure.environment.copy()
      next_environment.push((closure.parameter, argument))
      eval_typed(
        closure.sig,
        closure.ctx.extend(closure.parameter, closure.domain),
        closure.body,
        closure.codomain,
        next_environment,
      )
    }
    VNeutral(neutral) => Ok(VNeutral(NApp(neutral, domain, argument)))
    _ =>
      Err(
        TypeError::NormalizationError(
          message="attempted to apply a non-functional semantic value",
        ),
      )
  }
}

///|
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
  match head {
    @syntax.Bind(parameter, body) =>
      match infer(sig, ctx, arguments[0]) {
        Err(error) => Err(error)
        Ok(domain) => {
          let codomain = if arguments.length() == 1 {
            expected
          } else {
            match
              head_type_for_application(
                sig,
                ctx.extend(parameter, domain),
                body,
                arguments[1:].to_owned(),
                expected,
              ) {
              Err(error) => return Err(error)
              Ok(body_type) => body_type
            }
          }
          Ok(Ty::Arrow(domain, codomain))
        }
      }
    _ => infer(sig, ctx, head)
  }
}

///|
fn eval_typed(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  ty : Ty,
  environment : Array[(@core.Name, Value)],
) -> Result[Value, TypeError] {
  match term {
    @syntax.Value(Atom::UnitLit) => Ok(VUnit)
    @syntax.Value(Atom::Const(name)) => Ok(VNeutral(NConst(name)))
    @syntax.Variable(name) =>
      match env_lookup(environment, name) {
        Some(value) => Ok(value)
        None => Err(TypeError::UnboundVariable(name))
      }
    @syntax.Bind(parameter, body) =>
      match ty {
        Ty::Arrow(domain, codomain) =>
          Ok(VLam({ sig, ctx, environment, parameter, domain, codomain, body }))
        _ =>
          Err(
            TypeError::NormalizationError(
              message="lambda semantic value requires an arrow type",
            ),
          )
      }
    @syntax.Apply(head, arguments) => {
      if arguments.length() == 0 {
        return Err(TypeError::EmptyApplication)
      }
      let mut current_type = match
        head_type_for_application(sig, ctx, head, arguments, ty) {
        Ok(head_type) => head_type
        Err(error) => return Err(error)
      }
      let mut current = match
        eval_typed(sig, ctx, head, current_type, environment) {
        Ok(value) => value
        Err(error) => return Err(error)
      }
      for argument in arguments {
        match current_type {
          Ty::Arrow(domain, codomain) => {
            match check(sig, ctx, argument, domain) {
              Ok(_) => ()
              Err(error) => return Err(error)
            }
            let argument_value = match
              eval_typed(sig, ctx, argument, domain, environment) {
              Ok(value) => value
              Err(error) => return Err(error)
            }
            match apply_value_typed(current, domain, argument_value) {
              Ok(next) => current = next
              Err(error) => return Err(error)
            }
            current_type = codomain
          }
          _ => return Err(TypeError::ExpectedFunction(current_type))
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
  used : @hashset.HashSet[@core.Name],
  fresh : @core.Name,
) -> Result[Term, TypeError] {
  match ty {
    Ty::Base(_) =>
      match value {
        VNeutral(neutral) => quote_neutral(neutral, used)
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
        VNeutral(neutral) => quote_neutral(neutral, used)
        VLam(_) =>
          Err(
            TypeError::NormalizationError(
              message="function semantic value cannot inhabit unit type",
            ),
          )
      }
    Ty::Arrow(domain, codomain) => {
      let argument = reflect(domain, NFree(fresh))
      match apply_value_typed(value, domain, argument) {
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
      match apply_value_typed(value, domain, argument) {
        Ok(body_value) =>
          match reify_with_used(codomain, body_value, used.add(fresh)) {
            Ok(body) => Ok(@syntax.Bind(fresh, body))
            Err(error) => Err(error)
          }
        Err(error) => Err(error)
      }
    }
    _ => reify_with_name(ty, value, used, @core.Name::new("x"))
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
  let used = @syntax.all_names(term).union(context_names(ctx))
  match eval_typed(sig, ctx, term, ty, initial_environment(ctx)) {
    Ok(value) => reify(ty, value, used)
    Err(error) => Err(error)
  }
}
