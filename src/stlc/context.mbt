///|
/// Ordered variable typing entries. A later entry shadows an earlier one.
///
/// The type is abstract: its entries are not accessible outside the package.
/// Use `lookup`, `length`, and `to_array` to read it.
///
/// Contexts extended from one another share their array: `extend_with` pushes
/// onto it when `self` is the longest context stored there, and copies the
/// prefix otherwise. A context only reads its first `length` entries, and
/// entries are never changed once pushed, so a context cannot observe a longer
/// one built from it. Checking a term under `n` nested binders therefore takes
/// amortized `O(n)` time for the extensions instead of `O(n^2)` (issue #13).
struct TypeContext {
  /// The entries in insertion order; only the first `length` belong to this
  /// context.
  entries : Array[(@core.Name, Ty)]
  /// The number of entries of this context, counting shadowed ones.
  length : Int
}

///|
pub impl Eq for TypeContext with fn equal(self, other) {
  if self.length != other.length {
    return false
  }
  for i in 0..<self.length {
    if self.entries[i] != other.entries[i] {
      return false
    }
  }
  true
}

///|
/// Shows the entries in insertion order, as `{ entries: [...] }`.
pub impl Debug for TypeContext with fn to_repr(self) {
  @debug.Repr::record({ "entries": @debug.Repr(self.to_array()) })
}

///|
pub fn TypeContext::empty() -> TypeContext {
  { entries: [], length: 0, }
}

///|
/// Returns the context with `name : ty` added as its last entry. Takes
/// amortized constant time when `self` is the longest context extended so far
/// from the same empty context, as it is when a checker enters nested binders.
#alias(extend, deprecated="Use `TypeContext::extend_with` instead")
pub fn TypeContext::extend_with(
  self : TypeContext,
  name : @core.Name,
  ty : Ty,
) -> TypeContext {
  let entries = if self.entries.length() == self.length {
    self.entries
  } else {
    self.entries[0:self.length].to_owned()
  }
  entries.push((name, ty))
  { entries, length: self.length + 1, }
}

///|
pub fn TypeContext::lookup(self : TypeContext, name : @core.Name) -> Ty? {
  for i = self.length - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
/// Returns the number of entries, counting shadowed ones.
pub fn TypeContext::length(self : TypeContext) -> Int {
  self.length
}

///|
/// Returns the entries in insertion order as a fresh array. Changing the
/// returned array does not change `self`.
pub fn TypeContext::to_array(self : TypeContext) -> Array[(@core.Name, Ty)] {
  self.entries[0:self.length].to_owned()
}
