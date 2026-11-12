///|
#derive(Eq, Debug)
pub(all) enum Atom {
  UnitLit
  Const(@core.Name)
}

///|
pub type Term = @syntax.Term[Atom]
