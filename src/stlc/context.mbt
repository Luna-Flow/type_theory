///|
/// Ordered variable typing entries. A later entry shadows an earlier one.
///
/// The type is abstract: its entries are not accessible outside the package.
/// Use `lookup`, `length`, and `to_array` to read it.
struct TypeContext {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, Debug)

///|
pub fn TypeContext::empty() -> TypeContext {
  { entries: [], }
}

///|
#alias(extend, deprecated="Use `TypeContext::extend_with` instead")
pub fn TypeContext::extend_with(
  self : TypeContext,
  name : @core.Name,
  ty : Ty,
) -> TypeContext {
  let entries = self.entries.copy()
  entries.push((name, ty))
  { entries, }
}

///|
pub fn TypeContext::lookup(self : TypeContext, name : @core.Name) -> Ty? {
  for i = self.entries.length() - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
/// Returns the number of entries, counting shadowed ones.
pub fn TypeContext::length(self : TypeContext) -> Int {
  self.entries.length()
}

///|
/// Returns the entries in insertion order as a fresh array. Changing the
/// returned array does not change `self`.
pub fn TypeContext::to_array(self : TypeContext) -> Array[(@core.Name, Ty)] {
  self.entries.copy()
}
