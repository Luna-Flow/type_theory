///|
fn infer_apply(
  sig : Signature,
  ctx : TypeContext,
  head_type : Ty,
  arguments : Array[Term],
) -> Result[Ty, TypeError] {
  let mut current = head_type
  for argument in arguments {
    match current {
      Ty::Arrow(domain, codomain) =>
        match check(sig, ctx, argument, domain) {
          Ok(_) => current = codomain
          Err(error) => return Err(error)
        }
      _ => return Err(TypeError::ExpectedFunction(current))
    }
  }
  Ok(current)
}

///|
fn flatten_application(term : Term) -> (Term, Array[Term]) {
  match term {
    @syntax.Apply(head, arguments) => {
      let (base_head, base_arguments) = flatten_application(head)
      let merged = base_arguments.copy()
      merged.append(arguments)
      (base_head, merged)
    }
    _ => (term, [])
  }
}

///|
fn infer_lambda_application(
  sig : Signature,
  ctx : TypeContext,
  parameter : @core.Name,
  body : Term,
  arguments : Array[Term],
) -> Result[Ty, TypeError] {
  if arguments.length() == 0 {
    return Err(TypeError::EmptyApplication)
  }
  match infer(sig, ctx, arguments[0]) {
    Ok(argument_type) => {
      let next_ctx = ctx.extend(parameter, argument_type)
      if arguments.length() == 1 {
        infer(sig, next_ctx, body)
      } else {
        infer(sig, next_ctx, @syntax.Apply(body, arguments[1:].to_owned()))
      }
    }
    Err(error) => Err(error)
  }
}

///|
pub fn infer(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
) -> Result[Ty, TypeError] {
  match term {
    @syntax.Value(Atom::UnitLit) => Ok(Ty::Unit)
    @syntax.Value(Atom::Const(name)) =>
      match sig.lookup(name) {
        Some(ty) => Ok(ty)
        None => Err(TypeError::UnknownConstant(name))
      }
    @syntax.Variable(name) =>
      match ctx.lookup(name) {
        Some(ty) => Ok(ty)
        None => Err(TypeError::UnboundVariable(name))
      }
    @syntax.Apply(_, arguments) => {
      if arguments.length() == 0 {
        return Err(TypeError::EmptyApplication)
      }
      let (base_head, spine_arguments) = flatten_application(term)
      match base_head {
        @syntax.Bind(parameter, body) =>
          infer_lambda_application(sig, ctx, parameter, body, spine_arguments)
        _ =>
          match infer(sig, ctx, base_head) {
            Ok(head_type) => infer_apply(sig, ctx, head_type, spine_arguments)
            Err(error) => Err(error)
          }
      }
    }
    @syntax.Bind(_, _) => Err(TypeError::CannotInferLambda)
  }
}

///|
pub fn check(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  expected : Ty,
) -> Result[Unit, TypeError] {
  match (term, expected) {
    (@syntax.Bind(name, body), Ty::Arrow(domain, codomain)) =>
      check(sig, ctx.extend(name, domain), body, codomain)
    (_, _) =>
      match infer(sig, ctx, term) {
        Ok(actual) =>
          if actual == expected {
            Ok(())
          } else {
            Err(TypeError::TypeMismatch(expected~, actual~))
          }
        Err(error) => Err(error)
      }
  }
}
