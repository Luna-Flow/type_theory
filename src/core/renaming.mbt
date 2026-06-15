///|
/// A finite, simultaneous renaming. Unmapped names remain unchanged.
pub struct Renaming {
  entries : Array[(Name, Name)]
} derive(Eq, Debug)

///|
pub fn Renaming::empty() -> Renaming {
  { entries: [] }
}

///|
pub fn Renaming::singleton(from : Name, to_ : Name) -> Renaming {
  { entries: [(from, to_)] }
}

///|
/// Adds or replaces the image of `from`.
pub fn Renaming::set(self : Renaming, from : Name, to_ : Name) -> Renaming {
  let entries : Array[(Name, Name)] = []
  let mut replaced = false
  for entry in self.entries {
    if entry.0 == from {
      entries.push((from, to_))
      replaced = true
    } else {
      entries.push(entry)
    }
  }
  if !replaced {
    entries.push((from, to_))
  }
  { entries, }
}

///|
pub fn Renaming::apply(self : Renaming, name : Name) -> Name {
  for entry in self.entries {
    if entry.0 == name {
      return entry.1
    }
  }
  name
}

///|
/// Removes a source name from the renaming domain.
pub fn Renaming::without(self : Renaming, name : Name) -> Renaming {
  { entries: self.entries.filter(fn(entry) { entry.0 != name }) }
}

///|
/// Returns every source and target name mentioned by the renaming.
pub fn Renaming::support(self : Renaming) -> @hashset.HashSet[Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    result = result.add(entry.0).add(entry.1)
  }
  result
}

///|
/// Returns the targets of the finite renaming.
pub fn Renaming::targets(self : Renaming) -> @hashset.HashSet[Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    result = result.add(entry.1)
  }
  result
}

///|
/// Composition applies `self` first and `after` second.
pub fn Renaming::then(self : Renaming, after : Renaming) -> Renaming {
  let mut result = Renaming::empty()
  for entry in self.entries {
    result = result.set(entry.0, after.apply(entry.1))
  }
  for entry in after.entries {
    if self.apply(entry.0) == entry.0 {
      result = result.set(entry.0, entry.1)
    }
  }
  result
}
