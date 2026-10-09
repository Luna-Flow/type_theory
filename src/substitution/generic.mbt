///|
/// Finite simultaneous substitution for a downstream binding-aware AST.
///
/// The type is abstract: its entries are not accessible outside the package,
/// so each variable has at most one replacement. Use `get`, `length`, and
/// `to_array` to read it.
struct GenericSubstitution[N] {
  entries : Array[(@core.Name, N)]
}

///|
pub fn[N] GenericSubstitution::empty() -> GenericSubstitution[N] {
  { entries: [], }
}

///|
pub fn[N] GenericSubstitution::singleton(
  name : @core.Name,
  replacement : N,
) -> GenericSubstitution[N] {
  { entries: [(name, replacement)], }
}

///|
pub fn[N] GenericSubstitution::set(
  self : GenericSubstitution[N],
  name : @core.Name,
  replacement : N,
) -> GenericSubstitution[N] {
  let entries : Array[(@core.Name, N)] = []
  let mut replaced = false
  for entry in self.entries {
    if entry.0 == name {
      entries.push((name, replacement))
      replaced = true
    } else {
      entries.push(entry)
    }
  }
  if !replaced {
    entries.push((name, replacement))
  }
  { entries, }
}

///|
pub fn[N] GenericSubstitution::get(
  self : GenericSubstitution[N],
  name : @core.Name,
) -> N? {
  for entry in self.entries {
    if entry.0 == name {
      return Some(entry.1)
    }
  }
  None
}

///|
/// Returns the number of variables in the substitution domain.
pub fn[N] GenericSubstitution::length(self : GenericSubstitution[N]) -> Int {
  self.entries.length()
}

///|
/// Returns the `(name, replacement)` entries in insertion order as a fresh
/// array. Changing the returned array does not change `self`. The
/// replacement nodes are shared, not copied.
pub fn[N] GenericSubstitution::to_array(
  self : GenericSubstitution[N],
) -> Array[(@core.Name, N)] {
  self.entries.copy()
}

///|
pub fn[N] GenericSubstitution::without(
  self : GenericSubstitution[N],
  name : @core.Name,
) -> GenericSubstitution[N] {
  { entries: self.entries.filter(fn(entry) { entry.0 != name }), }
}

///|
/// Applies a simultaneous one-pass, capture-avoiding substitution.
///
/// Stack-safe in the nesting depth of the node and of the replacements.
pub fn[N : @syntax.BindingSyntax] GenericSubstitution::apply_once(
  self : GenericSubstitution[N],
  node : N,
) -> N {
  substitute(self.entries, node)
}
