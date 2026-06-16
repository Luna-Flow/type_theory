///|
pub fn normalize_checked(
  sig : Signature,
  ctx : TypeContext,
  term : Term,
  ty : Ty,
  max_steps : Int,
) -> Result[@rewrite.NormalizationResult[Atom], TypeError] {
  match check(sig, ctx, term, ty) {
    Ok(_) => Ok(@utlc_lambda.normalize(term, max_steps))
    Err(error) => Err(error)
  }
}
