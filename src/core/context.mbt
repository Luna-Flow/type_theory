///|
/// An ordered collection of names in scope.
pub struct Context {
  names : Array[Name]
} derive(Eq, Debug)

///|
pub fn Context::empty() -> Context {
  { names: [] }
}

///|
pub fn Context::from_array(names : Array[Name]) -> Context {
  { names: names.copy() }
}

///|
pub fn Context::extend(self : Context, name : Name) -> Context {
  let names = self.names.copy()
  names.push(name)
  { names, }
}

///|
pub fn Context::contains(self : Context, name : Name) -> Bool {
  self.names.contains(name)
}

///|
pub fn Context::length(self : Context) -> Int {
  self.names.length()
}

///|
pub fn Context::to_array(self : Context) -> Array[Name] {
  self.names.copy()
}

///|
/// A telescope records binders in dependency order.
pub struct Telescope[T] {
  entries : Array[(Name, T)]
}

///|
pub fn[T] Telescope::empty() -> Telescope[T] {
  { entries: [] }
}

///|
pub fn[T] Telescope::extend(
  self : Telescope[T],
  name : Name,
  annotation : T,
) -> Telescope[T] {
  let entries = self.entries.copy()
  entries.push((name, annotation))
  { entries, }
}

///|
pub fn[T] Telescope::length(self : Telescope[T]) -> Int {
  self.entries.length()
}

///|
pub fn[T] Telescope::to_array(self : Telescope[T]) -> Array[(Name, T)] {
  self.entries.copy()
}
