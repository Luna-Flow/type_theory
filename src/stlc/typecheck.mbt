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
/// Splits an application into its head and its whole argument spine, so that
/// `Apply(Apply(h, [a1]), [a2, a3])` and `Apply(h, [a1, a2, a3])` both become
/// `(h, [a1, a2, a3])`. The returned head is never an `Apply`; a term that is
/// not an application has an empty spine.
///
/// Fails with `EmptyApplication` if an `Apply` node of the spine has no
/// arguments, at the root or nested in the head.
fn application_spine(term : Term) -> Result[(Term, Array[Term]), TypeError] {
  match term {
    @syntax.Apply(head, arguments) => {
      if arguments.length() == 0 {
        return Err(TypeError::EmptyApplication)
      }
      match application_spine(head) {
        Ok((base, base_arguments)) => {
          let merged = base_arguments.copy()
          merged.append(arguments)
          Ok((base, merged))
        }
        Err(error) => Err(error)
      }
    }
    _ => Ok((term, []))
  }
}

///|
/// Renames the parameter of a redex `(λparameter. body) a1 a2 ... an` away
/// from the free variables of the trailing arguments `a2 ... an`.
///
/// The trailing arguments are typed after the parameter has been added to the
/// context. Without the renaming, a free occurrence of the parameter's name in
/// one of them would be captured and typed with the parameter's type.
fn rename_parameter_apart(
  ctx : TypeContext,
  parameter : @core.Name,
  body : Term,
  trailing : ArrayView[Term],
) -> (@core.Name, Term) {
  let mut trailing_free = @hashset.new()
  for argument in trailing {
    trailing_free = trailing_free.union(@syntax.free_variables(argument))
  }
  if !trailing_free.contains(parameter) {
    return (parameter, body)
  }
  let mut used = @syntax.all_names(body).add(parameter)
  for argument in trailing {
    used = used.union(@syntax.all_names(argument))
  }
  for entry in ctx.to_array() {
    used = used.add(entry.0)
  }
  let fresh = @core.fresh_name(parameter, used)
  match body.alpha_rename_bound(parameter, fresh) {
    Some(renamed) => (fresh, renamed)
    None => abort("fresh parameter name unexpectedly occurs in the body")
  }
}

///|
/// One step of the redex rule on a spine `(λx. b) a1 a2 ... an` (`n >= 1`):
/// the first argument `a1` has been inferred as `S`, and what is left to type
/// is the spine `b a2 ... an` under `x : S`.
priv struct RedexStep {
  /// The type `S` inferred for the first argument `a1`.
  domain : Ty
  /// The outer context extended with the parameter `x : S`.
  ctx : TypeContext
  /// The head of `b a2 ... an` after flattening; never an `Apply`.
  head : Term
  /// The arguments of `b` itself, followed by `a2 ... an`.
  arguments : Array[Term]
  /// How many leading entries of `arguments` are arguments of `b` itself.
  body_arity : Int
}

///|
/// Takes one step of the redex rule on the spine `(λparameter. body) arguments`.
///
/// The parameter is first renamed apart from the free variables of the trailing
/// arguments `a2 ... an` (issue #1), so that they can be typed in the extended
/// context without capture. The body is flattened together with the trailing
/// arguments (issue #7): a body that is itself an application, such as a redex
/// `(λy. c) d` consuming the outer arguments, joins the same spine.
fn redex_step(
  sig : Signature,
  ctx : TypeContext,
  parameter : @core.Name,
  body : Term,
  arguments : Array[Term],
) -> Result[RedexStep, TypeError] {
  if arguments.length() == 0 {
    return Err(TypeError::EmptyApplication)
  }
  let (parameter, body) = rename_parameter_apart(
    ctx,
    parameter,
    body,
    arguments[1:],
  )
  let domain = match infer(sig, ctx, arguments[0]) {
    Ok(argument_type) => argument_type
    Err(error) => return Err(error)
  }
  let (head, body_arguments) = match application_spine(body) {
    Ok(body_spine) => body_spine
    Err(error) => return Err(error)
  }
  let spine_arguments = body_arguments.copy()
  spine_arguments.append(arguments[1:].to_owned())
  Ok({
    domain,
    ctx: ctx.extend_with(parameter, domain),
    head,
    arguments: spine_arguments,
    body_arity: body_arguments.length(),
  })
}

///|
/// Infers the type of the flattened application `head arguments`, where `head`
/// is not an `Apply`. An empty spine infers `head` alone.
fn infer_spine(
  sig : Signature,
  ctx : TypeContext,
  head : Term,
  arguments : Array[Term],
) -> Result[Ty, TypeError] {
  if arguments.length() == 0 {
    return infer(sig, ctx, head)
  }
  match head {
    @syntax.Bind(parameter, body) =>
      match redex_step(sig, ctx, parameter, body, arguments) {
        Ok(step) => infer_spine(sig, step.ctx, step.head, step.arguments)
        Err(error) => Err(error)
      }
    _ =>
      match infer(sig, ctx, head) {
        Ok(head_type) => infer_apply(sig, ctx, head_type, arguments)
        Err(error) => Err(error)
      }
  }
}

///|
/// Checks the flattened application `head arguments` against `expected`, where
/// `head` is not an `Apply`. An empty spine checks `head` alone.
///
/// A lambda head takes one step of the redex rule in checking mode (issue #8):
/// the first argument is inferred, and the rest of the spine `b a2 ... an` is
/// checked against `expected` under the parameter, so a redex whose result is
/// a lambda is checked against the expected arrow instead of being inferred.
/// Any other head is inferred and its result compared with `expected`.
fn check_spine(
  sig : Signature,
  ctx : TypeContext,
  head : Term,
  arguments : Array[Term],
  expected : Ty,
) -> Result[Unit, TypeError] {
  if arguments.length() == 0 {
    return check(sig, ctx, head, expected)
  }
  match head {
    @syntax.Bind(parameter, body) =>
      match redex_step(sig, ctx, parameter, body, arguments) {
        Ok(step) =>
          check_spine(sig, step.ctx, step.head, step.arguments, expected)
        Err(error) => Err(error)
      }
    _ =>
      match infer_spine(sig, ctx, head, arguments) {
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
    @syntax.Apply(_, _) =>
      match application_spine(term) {
        Ok((head, arguments)) => infer_spine(sig, ctx, head, arguments)
        Err(error) => Err(error)
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
      check(sig, ctx.extend_with(name, domain), body, codomain)
    (@syntax.Apply(_, _), _) =>
      match application_spine(term) {
        Ok((head, arguments)) =>
          check_spine(sig, ctx, head, arguments, expected)
        Err(error) => Err(error)
      }
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
