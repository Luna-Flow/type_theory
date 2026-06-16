///|
pub(all) enum Ty {
  Base(@core.Name)
  Unit
  Arrow(Ty, Ty)
} derive(Eq, Debug)
