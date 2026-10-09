///|
/// A finite simultaneous substitution. Unmapped variables remain variables.
///
/// The type is abstract: its entries are not accessible outside the package,
/// so each variable has at most one replacement. Use `get`, `length`, and
/// `to_array` to read it.
struct Substitution[T] {
  entries : Array[(@core.Name, @syntax.Term[T])]
}

///|
pub fn[T] Substitution::empty() -> Substitution[T] {
  { entries: [], }
}

///|
pub fn[T] Substitution::singleton(
  name : @core.Name,
  replacement : @syntax.Term[T],
) -> Substitution[T] {
  { entries: [(name, replacement)], }
}

///|
pub fn[T] Substitution::set(
  self : Substitution[T],
  name : @core.Name,
  replacement : @syntax.Term[T],
) -> Substitution[T] {
  let entries : Array[(@core.Name, @syntax.Term[T])] = []
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
pub fn[T] Substitution::get(
  self : Substitution[T],
  name : @core.Name,
) -> @syntax.Term[T]? {
  for entry in self.entries {
    if entry.0 == name {
      return Some(entry.1)
    }
  }
  None
}

///|
/// Returns the number of variables in the substitution domain.
pub fn[T] Substitution::length(self : Substitution[T]) -> Int {
  self.entries.length()
}

///|
/// Returns the `(name, replacement)` entries in insertion order as a fresh
/// array. Changing the returned array does not change `self`. The
/// replacement terms are shared, not copied; treat their `Apply` argument
/// arrays as immutable.
pub fn[T] Substitution::to_array(
  self : Substitution[T],
) -> Array[(@core.Name, @syntax.Term[T])] {
  self.entries.copy()
}

///|
/// Removes a variable from the substitution domain under a shadowing binder.
pub fn[T] Substitution::without(
  self : Substitution[T],
  name : @core.Name,
) -> Substitution[T] {
  { entries: self.entries.filter(fn(entry) { entry.0 != name }), }
}

///|
/// Restricts the substitution to the supplied variable set.
pub fn[T] Substitution::restrict(
  self : Substitution[T],
  names : @hashset.HashSet[@core.Name],
) -> Substitution[T] {
  { entries: self.entries.filter(fn(entry) { names.contains(entry.0) }), }
}

///|
/// Applies a simultaneous, capture-avoiding substitution.
///
/// Stack-safe in the nesting depth of the term and of the replacements.
pub fn[T] Substitution::apply(
  self : Substitution[T],
  term : @syntax.Term[T],
) -> @syntax.Term[T] {
  substitute(self.entries, term)
}

///|
/// Composition applies `self` first and `after` second.
pub fn[T] Substitution::then(
  self : Substitution[T],
  after : Substitution[T],
) -> Substitution[T] {
  let mut result = Substitution::empty()
  for entry in self.entries {
    result = result.set(entry.0, after.apply(entry.1))
  }
  for entry in after.entries {
    if self.get(entry.0) is None {
      result = result.set(entry.0, entry.1)
    }
  }
  result
}

///|
/// Embeds a renaming as a substitution over generic terms.
pub fn[T] from_renaming(
  names : Array[@core.Name],
  renaming : @core.Renaming,
) -> Substitution[T] {
  let mut result = Substitution::empty()
  for name in names {
    let renamed = renaming.apply(name)
    if renamed != name {
      result = result.set(name, @syntax.Variable(renamed))
    }
  }
  result
}
