///|
pub(all) enum Atom {
  UnitLit
  Const(@core.Name)
} derive(Eq, Debug)

///|
pub type Term = @syntax.Term[Atom]
