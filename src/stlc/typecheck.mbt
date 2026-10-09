///|
/// Splits an application into its head and its whole argument spine, so that
/// `Apply(Apply(h, [a1]), [a2, a3])` and `Apply(h, [a1, a2, a3])` both become
/// `(h, [a1, a2, a3])`. The returned head is never an `Apply`; a term that is
/// not an application has an empty spine.
///
/// Fails with `EmptyApplication` if an `Apply` node of the spine has no
/// arguments, at the root or nested in the head.
///
/// The heads are followed with a loop, and the argument arrays are joined once
/// at the end, innermost first: the host stack depth is constant and the time
/// is linear in the size of the spine.
fn application_spine(term : Term) -> Result[(Term, Array[Term]), TypeError] {
  let layers : Array[Array[Term]] = []
  let head = for current = term {
    match current {
      @syntax.Apply(head, arguments) => {
        if arguments.length() == 0 {
          return Err(TypeError::EmptyApplication)
        }
        layers.push(arguments)
        continue head
      }
      _ => break current
    }
  }
  let merged : Array[Term] = []
  for i = layers.length() - 1; i >= 0; i = i - 1 {
    merged.append(layers[i])
  }
  Ok((head, merged))
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
  /// The outer context extended with the parameter `x : S`.
  ctx : TypeContext
  /// The head of `b a2 ... an` after flattening; never an `Apply`.
  head : Term
  /// The arguments of `b` itself, followed by `a2 ... an`.
  arguments : Array[Term]
}

///|
/// The part of the redex rule before the first argument is inferred: the
/// parameter of `(λparameter. body) arguments` is renamed apart from the free
/// variables of the trailing arguments `a2 ... an` (issue #1), so that they can
/// be typed in the extended context without capture.
fn redex_prepare(
  ctx : TypeContext,
  parameter : @core.Name,
  body : Term,
  arguments : Array[Term],
) -> Result[(@core.Name, Term), TypeError] {
  if arguments.length() == 0 {
    return Err(TypeError::EmptyApplication)
  }
  Ok(rename_parameter_apart(ctx, parameter, body, arguments[1:]))
}

///|
/// The part of the redex rule after the first argument has been inferred as
/// `domain`. The body is flattened together with the trailing arguments
/// (issue #7): a body that is itself an application, such as a redex
/// `(λy. c) d` consuming the outer arguments, joins the same spine.
fn redex_finish(
  ctx : TypeContext,
  parameter : @core.Name,
  body : Term,
  arguments : Array[Term],
  domain : Ty,
) -> Result[RedexStep, TypeError] {
  let (head, body_arguments) = match application_spine(body) {
    Ok(body_spine) => body_spine
    Err(error) => return Err(error)
  }
  let spine_arguments = body_arguments.copy()
  spine_arguments.append(arguments[1:].to_owned())
  Ok({
    ctx: ctx.extend_with(parameter, domain),
    head,
    arguments: spine_arguments,
  })
}

///|
/// Public typing is a view of the single typed-plan elaborator. The private
/// machine lives in `typed_plan.mbt`; these wrappers discard the plan after
/// preserving its inferred type or successful check.
pub fn infer(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
) -> Result[Ty, TypeError] {
  match build_typed_plan(sig, InferPlan(ctx, term)) {
    Ok(plan) => Ok(plan.ty())
    Err(error) => Err(error)
  }
}

///|
pub fn check(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  expected : Ty,
) -> Result[Unit, TypeError] {
  match build_typed_plan(sig, CheckPlan(ctx, term, expected)) {
    Ok(_) => Ok(())
    Err(error) => Err(error)
  }
}
