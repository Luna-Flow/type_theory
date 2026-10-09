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

// Bounded-stack type checking (issue #13).
//
// Bidirectional checking is specified by mutually recursive functions:
//
// - `infer(Γ, t)` and `check(Γ, t, A)` on a term;
// - `infer_spine(Γ, h, ā)` and `check_spine(Γ, h, ā, A)` on a flattened
//   application, where a lambda head takes one step of the redex rule:
//   infer the first argument, then continue with the rest of the spine under
//   the parameter;
// - `infer_apply(Γ, A, ā)`, which checks the arguments of a non-lambda head
//   of type `A` one after the other against the domains of `A`.
//
// Implemented as host recursion, a term nested `d` levels deep (binders,
// argument positions or redexes) needs `d` host frames, and the js and wasm
// stacks overflow at a depth of a few thousand.
//
// The functions are run instead as one loop over an explicit continuation, as
// the NbE evaluator of `utlc/nbe` does:
//
// - `CheckControl` is the next thing to do: one of the functions above, or a
//   result (`Inferred` or `Checked`) handed to the innermost frame.
// - `CheckFrame` is the rest of a caller that still has to run when a call
//   returns. The frames live in a heap `Array`.
//
// A call in tail position replaces the control and pushes nothing; a call
// whose result is still needed pushes the frame for the rest of the caller
// first. Every step happens in the order of the recursive definition, and no
// error is ever caught and replaced, so the first error met is the one the
// recursive functions returned: results, including which `TypeError` is
// reported, are unchanged.

///|
/// The next step of the type checking machine.
priv enum CheckControl {
  /// `infer(ctx, term)`.
  Infer(TypeContext, Term)
  /// `check(ctx, term, expected)`.
  Check(TypeContext, Term, Ty)
  /// `infer_spine(ctx, head, arguments)`; `head` is not an `Apply`.
  InferSpine(TypeContext, Term, Array[Term])
  /// `check_spine(ctx, head, arguments, expected)`; `head` is not an `Apply`.
  CheckSpine(TypeContext, Term, Array[Term], Ty)
  /// An inference returned this type.
  Inferred(Ty)
  /// A check succeeded.
  Checked
}

///|
/// A pending step of the type checking machine, waiting for a result.
priv enum CheckFrame {
  /// Waiting for the type of a non-lambda spine head: check `arguments`
  /// against its domains (`infer_apply`).
  ApplyHeadType(TypeContext, Array[Term])
  /// Waiting for the check of argument `index` of a spine; `codomain` is the
  /// type of the application up to and including that argument.
  ArgumentChecked(TypeContext, Array[Term], Int, Ty)
  /// Waiting for an inferred type to compare with `expected`.
  CompareWith(Ty)
  /// Waiting for the type of the first argument of the redex
  /// `(λparameter. body) arguments`, whose parameter has been renamed apart;
  /// then the rest of the spine is inferred, or checked against the type.
  RedexArgument(TypeContext, @core.Name, Term, Array[Term], Ty?)
}

///|
/// `infer_apply` from argument `index` on, where the application up to that
/// argument has type `current`: the next control, after pushing the frame
/// for the arguments after it.
fn apply_arguments(
  frames : Array[CheckFrame],
  ctx : TypeContext,
  arguments : Array[Term],
  index : Int,
  current : Ty,
) -> Result[CheckControl, TypeError] {
  if index == arguments.length() {
    return Ok(Inferred(current))
  }
  match current {
    Ty::Arrow(domain, codomain) => {
      frames.push(ArgumentChecked(ctx, arguments, index, codomain))
      Ok(Check(ctx, arguments[index], domain))
    }
    _ => Err(TypeError::ExpectedFunction(current))
  }
}

///|
/// Runs the type checking machine from `start`. Returns `Some(ty)` when the
/// outermost call is an inference and `None` when it is a check. The host
/// stack depth is constant; pending work is kept in a heap array of frames.
fn run_typing(sig : Signature, start : CheckControl) -> Result[Ty?, TypeError] {
  let frames : Array[CheckFrame] = []
  for control = start {
    match control {
      Infer(ctx, term) =>
        match term {
          @syntax.Value(Atom::UnitLit) => continue Inferred(Ty::Unit)
          @syntax.Value(Atom::Const(name)) =>
            match sig.lookup(name) {
              Some(ty) => continue Inferred(ty)
              None => break Err(TypeError::UnknownConstant(name))
            }
          @syntax.Variable(name) =>
            match ctx.lookup(name) {
              Some(ty) => continue Inferred(ty)
              None => break Err(TypeError::UnboundVariable(name))
            }
          @syntax.Apply(_, _) =>
            match application_spine(term) {
              Ok((head, arguments)) => continue InferSpine(ctx, head, arguments)
              Err(error) => break Err(error)
            }
          @syntax.Bind(_, _) => break Err(TypeError::CannotInferLambda)
        }
      Check(ctx, term, expected) =>
        match (term, expected) {
          (@syntax.Bind(name, body), Ty::Arrow(domain, codomain)) =>
            continue Check(ctx.extend_with(name, domain), body, codomain)
          (@syntax.Apply(_, _), _) =>
            match application_spine(term) {
              Ok((head, arguments)) =>
                continue CheckSpine(ctx, head, arguments, expected)
              Err(error) => break Err(error)
            }
          (_, _) => {
            frames.push(CompareWith(expected))
            continue Infer(ctx, term)
          }
        }
      InferSpine(ctx, head, arguments) => {
        if arguments.length() == 0 {
          continue Infer(ctx, head)
        }
        match head {
          @syntax.Bind(parameter, body) =>
            match redex_prepare(ctx, parameter, body, arguments) {
              Ok((parameter, body)) => {
                frames.push(
                  RedexArgument(ctx, parameter, body, arguments, None),
                )
                continue Infer(ctx, arguments[0])
              }
              Err(error) => break Err(error)
            }
          _ => {
            frames.push(ApplyHeadType(ctx, arguments))
            continue Infer(ctx, head)
          }
        }
      }
      CheckSpine(ctx, head, arguments, expected) => {
        if arguments.length() == 0 {
          continue Check(ctx, head, expected)
        }
        match head {
          @syntax.Bind(parameter, body) =>
            match redex_prepare(ctx, parameter, body, arguments) {
              Ok((parameter, body)) => {
                frames.push(
                  RedexArgument(ctx, parameter, body, arguments, Some(expected)),
                )
                continue Infer(ctx, arguments[0])
              }
              Err(error) => break Err(error)
            }
          _ => {
            frames.push(CompareWith(expected))
            continue InferSpine(ctx, head, arguments)
          }
        }
      }
      Inferred(ty) =>
        match frames.pop() {
          None => break Ok(Some(ty))
          Some(ApplyHeadType(ctx, arguments)) =>
            match apply_arguments(frames, ctx, arguments, 0, ty) {
              Ok(next) => continue next
              Err(error) => break Err(error)
            }
          Some(CompareWith(expected)) =>
            if ty == expected {
              continue Checked
            } else {
              break Err(TypeError::TypeMismatch(expected~, actual=ty))
            }
          Some(RedexArgument(ctx, parameter, body, arguments, mode)) =>
            match redex_finish(ctx, parameter, body, arguments, ty) {
              Ok(step) =>
                match mode {
                  None =>
                    continue InferSpine(step.ctx, step.head, step.arguments)
                  Some(expected) =>
                    continue CheckSpine(
                        step.ctx,
                        step.head,
                        step.arguments,
                        expected,
                      )
                }
              Err(error) => break Err(error)
            }
          Some(ArgumentChecked(_, _, _, _)) =>
            abort("an argument check cannot return a type")
        }
      Checked =>
        match frames.pop() {
          None => break Ok(None)
          Some(ArgumentChecked(ctx, arguments, index, codomain)) =>
            match apply_arguments(frames, ctx, arguments, index + 1, codomain) {
              Ok(next) => continue next
              Err(error) => break Err(error)
            }
          Some(_) => abort("only an argument check waits for a check")
        }
    }
  }
}

///|
/// Infers the type of `term`. The host stack depth does not grow with the
/// nesting depth of `term`.
pub fn infer(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
) -> Result[Ty, TypeError] {
  match run_typing(sig, Infer(ctx, term)) {
    Ok(Some(ty)) => Ok(ty)
    Ok(None) => abort("an inference must return a type")
    Err(error) => Err(error)
  }
}

///|
/// Checks `term` against `expected`. The host stack depth does not grow with
/// the nesting depth of `term` or `expected`.
pub fn check(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  expected : Ty,
) -> Result[Unit, TypeError] {
  match run_typing(sig, Check(ctx, term, expected)) {
    Ok(None) => Ok(())
    Ok(Some(_)) => abort("a check must not return a type")
    Err(error) => Err(error)
  }
}
