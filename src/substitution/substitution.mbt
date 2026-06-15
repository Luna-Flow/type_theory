///|
/// A finite simultaneous substitution. Unmapped variables remain variables.
pub struct Substitution[T] {
  entries : Array[(@core.Name, @syntax.Term[T])]
}

///|
pub fn[T] Substitution::empty() -> Substitution[T] {
  { entries: [] }
}

///|
pub fn[T] Substitution::singleton(
  name : @core.Name,
  replacement : @syntax.Term[T],
) -> Substitution[T] {
  { entries: [(name, replacement)] }
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
/// Removes a variable from the substitution domain under a shadowing binder.
pub fn[T] Substitution::without(
  self : Substitution[T],
  name : @core.Name,
) -> Substitution[T] {
  { entries: self.entries.filter(fn(entry) { entry.0 != name }) }
}

///|
/// Restricts the substitution to the supplied variable set.
pub fn[T] Substitution::restrict(
  self : Substitution[T],
  names : @hashset.HashSet[@core.Name],
) -> Substitution[T] {
  { entries: self.entries.filter(fn(entry) { names.contains(entry.0) }) }
}

///|
fn[T] Substitution::relevant_range_free_variables(
  self : Substitution[T],
  body_free : @hashset.HashSet[@core.Name],
) -> @hashset.HashSet[@core.Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    if body_free.contains(entry.0) {
      result = result.union(@syntax.free_variables(entry.1))
    }
  }
  result
}

///|
/// Names mentioned by the substitution domain or any replacement term.
fn[T] Substitution::support(
  self : Substitution[T],
) -> @hashset.HashSet[@core.Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    result = result.add(entry.0).union(@syntax.all_names(entry.1))
  }
  result
}

///|
/// Applies a simultaneous, capture-avoiding substitution.
pub fn[T] Substitution::apply(
  self : Substitution[T],
  term : @syntax.Term[T],
) -> @syntax.Term[T] {
  match term {
    Value(value) => Value(value)
    Variable(name) => self.get(name).unwrap_or(Variable(name))
    Apply(head, arguments) =>
      Apply(
        self.apply(head),
        arguments.map(fn(argument) { self.apply(argument) }),
      )
    Bind(name, body) => {
      let under_binder = self.without(name)
      let body_free = @syntax.free_variables(body)
      let range_free = under_binder.relevant_range_free_variables(body_free)
      if range_free.contains(name) {
        let used = under_binder
          .support()
          .union(@syntax.all_names(body))
          .add(name)
        let fresh = @core.fresh_name(name, used)
        match body.alpha_rename_bound(name, fresh) {
          Some(renamed_body) =>
            Bind(fresh, under_binder.without(fresh).apply(renamed_body))
          None => abort("fresh name unexpectedly occurs in substitution body")
        }
      } else {
        Bind(name, under_binder.apply(body))
      }
    }
  }
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
