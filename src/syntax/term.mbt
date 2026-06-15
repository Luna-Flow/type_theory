///|
/// Generic syntax with domain values, variables, application, and binding.
///
/// `T` is treated as a closed atom with respect to `Name`: free-variable
/// analysis, renaming, substitution, and alpha-equivalence do not inspect it.
pub(all) enum Term[T] {
  Value(T)
  Variable(@core.Name)
  Apply(Term[T], Array[Term[T]])
  Bind(@core.Name, Term[T])
} derive(Eq, Debug)

///|
/// Maps domain values without changing variables or binding structure.
pub fn[T, U] Term::map_values(self : Term[T], f : (T) -> U) -> Term[U] {
  match self {
    Value(value) => Value(f(value))
    Variable(name) => Variable(name)
    Apply(head, arguments) =>
      Apply(head.map_values(f), arguments.map(fn(term) { term.map_values(f) }))
    Bind(name, body) => Bind(name, body.map_values(f))
  }
}

///|
fn[T] rename_free_visit(term : Term[T], renaming : @core.Renaming) -> Term[T] {
  match term {
    Value(value) => Value(value)
    Variable(name) => Variable(renaming.apply(name))
    Apply(head, arguments) =>
      Apply(
        rename_free_visit(head, renaming),
        arguments.map(fn(argument) { rename_free_visit(argument, renaming) }),
      )
    Bind(name, body) => {
      let under_binder = renaming.without(name)
      if under_binder.targets().contains(name) {
        let used = all_names(body).union(under_binder.support()).add(name)
        let fresh = @core.fresh_name(name, used)
        let renamed_body = rename_bound_visit(body, true, name, fresh)
        Bind(fresh, rename_free_visit(renamed_body, under_binder))
      } else {
        Bind(name, rename_free_visit(body, under_binder))
      }
    }
  }
}

///|
/// Renames free occurrences. A binder shadows a source name of the renaming.
pub fn[T] Term::rename_free(
  self : Term[T],
  renaming : @core.Renaming,
) -> Term[T] {
  rename_free_visit(self, renaming)
}

///|
fn[T] rename_bound_visit(
  term : Term[T],
  active : Bool,
  from : @core.Name,
  to_ : @core.Name,
) -> Term[T] {
  match term {
    Value(value) => Value(value)
    Variable(name) =>
      if active && name == from {
        Variable(to_)
      } else {
        Variable(name)
      }
    Apply(head, arguments) =>
      Apply(
        rename_bound_visit(head, active, from, to_),
        arguments.map(fn(argument) {
          rename_bound_visit(argument, active, from, to_)
        }),
      )
    Bind(name, body) => {
      let next_active = active && name != from
      Bind(name, rename_bound_visit(body, next_active, from, to_))
    }
  }
}

///|
/// Alpha-renames occurrences bound by an enclosing binder.
///
/// Returns `None` when `to_` already occurs in the body and could cause
/// capture. Passing `from == to_` is identity.
pub fn[T] Term::alpha_rename_bound(
  self : Term[T],
  from : @core.Name,
  to_ : @core.Name,
) -> Term[T]? {
  if from == to_ {
    Some(self)
  } else if all_names(self).contains(to_) {
    None
  } else {
    Some(rename_bound_visit(self, true, from, to_))
  }
}
