///|
#derive(Eq, Debug)
pub(all) enum TypeError {
  UnboundVariable(@core.Name)
  UnknownConstant(@core.Name)
  CannotInferLambda
  ExpectedFunction(Ty)
  TypeMismatch(expected~ : Ty, actual~ : Ty)
  EmptyApplication
  ScopeError(@debruijn.ScopeError)
  NormalizationError(message~ : String)
}
