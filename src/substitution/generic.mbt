///|
/// Finite simultaneous substitution for a downstream binding-aware AST.
pub struct GenericSubstitution[N] {
  entries : Array[(@core.Name, N)]
}

///|
pub fn[N] GenericSubstitution::empty() -> GenericSubstitution[N] {
  { entries: [] }
}

///|
pub fn[N] GenericSubstitution::singleton(
  name : @core.Name,
  replacement : N,
) -> GenericSubstitution[N] {
  { entries: [(name, replacement)] }
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
pub fn[N] GenericSubstitution::without(
  self : GenericSubstitution[N],
  name : @core.Name,
) -> GenericSubstitution[N] {
  { entries: self.entries.filter(fn(entry) { entry.0 != name }) }
}

///|
fn[N : @syntax.BindingSyntax] GenericSubstitution::relevant_range_free(
  self : GenericSubstitution[N],
  body_free : @hashset.HashSet[@core.Name],
) -> @hashset.HashSet[@core.Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    if body_free.contains(entry.0) {
      result = result.union(@syntax.generic_free_variables(entry.1))
    }
  }
  result
}

///|
fn[N : @syntax.BindingSyntax] GenericSubstitution::support(
  self : GenericSubstitution[N],
) -> @hashset.HashSet[@core.Name] {
  let mut result = @hashset.new()
  for entry in self.entries {
    result = result.add(entry.0).union(@syntax.generic_all_names(entry.1))
  }
  result
}

///|
/// Applies a simultaneous one-pass, capture-avoiding substitution.
pub fn[N : @syntax.BindingSyntax] GenericSubstitution::apply_once(
  self : GenericSubstitution[N],
  node : N,
) -> N {
  match @syntax.BindingSyntax::project(node) {
    @syntax.BindingView::Opaque => node
    @syntax.BindingView::Variable(name) => self.get(name).unwrap_or(node)
    @syntax.BindingView::Apply(head, arguments) =>
      @syntax.BindingSyntax::apply(
        self.apply_once(head),
        arguments.map(fn(argument) { self.apply_once(argument) }),
      )
    @syntax.BindingView::Bind(name, body) => {
      let under_binder = self.without(name)
      let body_free = @syntax.generic_free_variables(body)
      let range_free = under_binder.relevant_range_free(body_free)
      if range_free.contains(name) {
        let used = under_binder
          .support()
          .union(@syntax.generic_all_names(body))
          .add(name)
        let fresh = @core.fresh_name(name, used)
        match @syntax.generic_alpha_rename_bound(body, name, fresh) {
          Some(renamed_body) =>
            @syntax.BindingSyntax::bind(
              fresh,
              under_binder.without(fresh).apply_once(renamed_body),
            )
          None => abort("fresh name unexpectedly occurs in generic syntax")
        }
      } else {
        @syntax.BindingSyntax::bind(name, under_binder.apply_once(body))
      }
    }
  }
}
