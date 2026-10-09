///|
pub(all) enum Ty {
  Base(@core.Name)
  Unit
  Arrow(Ty, Ty)
} derive(Debug)

///|
/// Structural equality of types.
///
/// Written by hand instead of derived so that it compares deep arrow types
/// with a heap array of pending pairs instead of host recursion (issue #13).
/// Pairs are compared left to right, and a pair of physically equal types is
/// equal without being traversed.
pub impl Eq for Ty with fn equal(self, other) {
  let pending = [(self, other)]
  while pending.pop() is Some((left, right)) {
    if physical_equal(left, right) {
      continue
    }
    match (left, right) {
      (Base(left_name), Base(right_name)) =>
        if left_name != right_name {
          return false
        }
      (Unit, Unit) => ()
      (Arrow(left_domain, left_codomain), Arrow(right_domain, right_codomain)) => {
        pending.push((left_codomain, right_codomain))
        pending.push((left_domain, right_domain))
      }
      _ => return false
    }
  }
  true
}
