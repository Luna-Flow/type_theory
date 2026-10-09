///|
/// Private elaboration of the bidirectional rules. Types are recorded once;
/// evaluation never calls infer/check. A redex is a strict let over its
/// renamed body joined with the trailing arguments (the checker redex rule).
priv enum TypedPlan {
  PlanValue(Atom, Ty)
  PlanVariable(@core.Name, Ty)
  PlanBind(@core.Name, Ty, TypedPlan)
  PlanApply(TypedPlan, Ty, TypedPlan, Ty)
  PlanLet(@core.Name, @core.Name, TypedPlan, TypedPlan, Ty)
}

///|
fn TypedPlan::ty(self : TypedPlan) -> Ty {
  match self {
    PlanValue(_, ty)
    | PlanVariable(_, ty)
    | PlanBind(_, ty, _)
    | PlanApply(_, _, _, ty)
    | PlanLet(_, _, _, _, ty) => ty
  }
}

///|
priv enum PlanControl {
  InferPlan(TypeContext, Term)
  CheckPlan(TypeContext, Term, Ty)
  SpinePlan(TypeContext, Term, Array[Term], Ty?)
  ReturnPlan(TypedPlan)
}

///|
priv enum PlanFrame {
  PlanHead(TypeContext, Array[Term])
  PlanArgument(TypeContext, Array[Term], Int, TypedPlan, Ty, Ty)
  PlanCompare(Ty)
  PlanRedexFirst(TypeContext, @core.Name, @core.Name, Term, Array[Term], Ty?)
  PlanRedexRest(@core.Name, @core.Name, TypedPlan)
  PlanBindBody(@core.Name, Ty)
}

///|
fn plan_arguments(
  frames : Array[PlanFrame],
  ctx : TypeContext,
  arguments : Array[Term],
  index : Int,
  function : TypedPlan,
) -> Result[PlanControl, TypeError] {
  if index == arguments.length() {
    return Ok(ReturnPlan(function))
  }
  match function.ty() {
    Ty::Arrow(domain, codomain) => {
      frames.push(
        PlanArgument(ctx, arguments, index, function, domain, codomain),
      )
      Ok(CheckPlan(ctx, arguments[index], domain))
    }
    actual => Err(TypeError::ExpectedFunction(actual))
  }
}

///|
/// Single source of typing rules for infer, check and normalization:
/// rename, infer the first
/// redex argument, flatten the body, then check/infer the remaining spine.
/// Successful continuations additionally assemble a typed execution plan.
fn build_typed_plan(
  sig : Signature,
  start : PlanControl,
) -> Result[TypedPlan, TypeError] {
  let frames : Array[PlanFrame] = []
  for control = start {
    match control {
      InferPlan(ctx, term) =>
        match term {
          @syntax.Value(Atom::UnitLit) =>
            continue ReturnPlan(PlanValue(Atom::UnitLit, Ty::Unit))
          @syntax.Value(Atom::Const(name)) =>
            match sig.lookup(name) {
              Some(ty) => continue ReturnPlan(PlanValue(Atom::Const(name), ty))
              None => break Err(TypeError::UnknownConstant(name))
            }
          @syntax.Variable(name) =>
            match ctx.lookup(name) {
              Some(ty) => continue ReturnPlan(PlanVariable(name, ty))
              None => break Err(TypeError::UnboundVariable(name))
            }
          @syntax.Apply(_, _) =>
            match application_spine(term) {
              Ok((head, arguments)) =>
                continue SpinePlan(ctx, head, arguments, None)
              Err(error) => break Err(error)
            }
          @syntax.Bind(_, _) => break Err(TypeError::CannotInferLambda)
        }
      CheckPlan(ctx, term, expected) =>
        match (term, expected) {
          (@syntax.Bind(name, body), Ty::Arrow(domain, codomain)) => {
            frames.push(PlanBindBody(name, expected))
            continue CheckPlan(ctx.extend_with(name, domain), body, codomain)
          }
          (@syntax.Apply(_, _), _) =>
            match application_spine(term) {
              Ok((head, arguments)) =>
                continue SpinePlan(ctx, head, arguments, Some(expected))
              Err(error) => break Err(error)
            }
          (_, _) => {
            frames.push(PlanCompare(expected))
            continue InferPlan(ctx, term)
          }
        }
      SpinePlan(ctx, head, arguments, mode) => {
        if arguments.length() == 0 {
          match mode {
            None => continue InferPlan(ctx, head)
            Some(expected) => continue CheckPlan(ctx, head, expected)
          }
        }
        match head {
          @syntax.Bind(original, body) =>
            match redex_prepare(ctx, original, body, arguments) {
              Ok((parameter, body)) => {
                frames.push(
                  PlanRedexFirst(
                    ctx, parameter, original, body, arguments, mode,
                  ),
                )
                continue InferPlan(ctx, arguments[0])
              }
              Err(error) => break Err(error)
            }
          _ => {
            match mode {
              Some(expected) => frames.push(PlanCompare(expected))
              None => ()
            }
            frames.push(PlanHead(ctx, arguments))
            continue InferPlan(ctx, head)
          }
        }
      }
      ReturnPlan(plan) =>
        match frames.pop() {
          None => break Ok(plan)
          Some(PlanHead(ctx, arguments)) =>
            match plan_arguments(frames, ctx, arguments, 0, plan) {
              Ok(next) => continue next
              Err(error) => break Err(error)
            }
          Some(PlanArgument(ctx, arguments, index, function, domain, codomain)) => {
            let applied = PlanApply(function, domain, plan, codomain)
            match plan_arguments(frames, ctx, arguments, index + 1, applied) {
              Ok(next) => continue next
              Err(error) => break Err(error)
            }
          }
          Some(PlanCompare(expected)) => {
            if plan.ty() != expected {
              break Err(TypeError::TypeMismatch(expected~, actual=plan.ty()))
            }
            continue ReturnPlan(plan)
          }
          Some(PlanBindBody(name, ty)) =>
            continue ReturnPlan(PlanBind(name, ty, plan))
          Some(PlanRedexFirst(ctx, parameter, original, body, arguments, mode)) => {
            let step = match
              redex_finish(ctx, parameter, body, arguments, plan.ty()) {
              Ok(step) => step
              Err(error) => break Err(error)
            }
            frames.push(PlanRedexRest(parameter, original, plan))
            continue SpinePlan(step.ctx, step.head, step.arguments, mode)
          }
          Some(PlanRedexRest(parameter, original, argument)) =>
            continue ReturnPlan(
                PlanLet(parameter, original, argument, plan, plan.ty()),
              )
        }
    }
  }
}
