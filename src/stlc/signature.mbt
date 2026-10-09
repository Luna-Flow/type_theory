///|
/// Ordered constant typing entries. A later entry shadows an earlier one.
///
/// The type is abstract: its entries are not accessible outside the package.
/// Use `lookup`, `length`, and `to_array` to read it.
struct Signature {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, Debug)

///|
pub fn Signature::empty() -> Signature {
  { entries: [], }
}

///|
#alias(extend, deprecated="Use `Signature::extend_with` instead")
pub fn Signature::extend_with(
  self : Signature,
  name : @core.Name,
  ty : Ty,
) -> Signature {
  let entries = self.entries.copy()
  entries.push((name, ty))
  { entries, }
}

///|
pub fn Signature::lookup(self : Signature, name : @core.Name) -> Ty? {
  for i = self.entries.length() - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
/// Returns the number of entries, counting shadowed ones.
pub fn Signature::length(self : Signature) -> Int {
  self.entries.length()
}

///|
/// Returns the entries in insertion order as a fresh array. Changing the
/// returned array does not change `self`.
pub fn Signature::to_array(self : Signature) -> Array[(@core.Name, Ty)] {
  self.entries.copy()
}
