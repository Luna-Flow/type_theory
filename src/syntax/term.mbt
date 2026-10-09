///|
/// Generic syntax with domain values, variables, application, and binding.
///
/// `T` is treated as a closed atom with respect to `Name`: free-variable
/// analysis, renaming, substitution, and alpha-equivalence do not inspect it.
///
/// Terms are shared, not copied: operations may return a term, or a subterm,
/// that is also held by an argument or by a library value such as a
/// substitution or a reduction trace. Treat the argument array of `Apply` as
/// immutable; build a new term instead of changing it in place.
pub(all) enum Term[T] {
  Value(T)
  Variable(@core.Name)
  Apply(Term[T], Array[Term[T]])
  Bind(@core.Name, Term[T])
} derive(Debug)

///|
/// Structural equality: the same constructors, names, and arities, with
/// values compared by `T`'s `==`. It is the derived equality, run with an
/// explicit work stack so that it is stack-safe in the nesting depth.
///
/// There is no shortcut for physically equal subterms: a `Double` NaN payload
/// makes a term unequal to itself, exactly as with the derived `==`.
pub impl[T : Eq] Eq for Term[T] with fn equal(self, other) {
  let pending = [(self, other)]
  while pending.pop() is Some(pair) {
    match pair {
      (Value(a), Value(b)) => if a != b { return false }
      (Variable(a), Variable(b)) => if a != b { return false }
      (Apply(a, a_args), Apply(b, b_args)) => {
        if a_args.length() != b_args.length() {
          return false
        }
        // compare the heads first, then the arguments left to right
        for i = a_args.length() - 1; i >= 0; i = i - 1 {
          pending.push((a_args[i], b_args[i]))
        }
        pending.push((a, b))
      }
      (Bind(a, a_body), Bind(b, b_body)) => {
        if a != b {
          return false
        }
        pending.push((a_body, b_body))
      }
      _ => return false
    }
  }
  true
}

///|
/// A pending step of `map_values`; see `rebuild` for the scheme.
priv enum MapTask[T] {
  Visit(Term[T])
  BuildApply(Int)
  BuildBind(@core.Name)
}

///|
/// Maps domain values without changing variables or binding structure.
///
/// `f` is called once per value, in the order the values occur (pre-order,
/// head before arguments).
pub fn[T, U] Term::map_values(self : Term[T], f : (T) -> U) -> Term[U] {
  let tasks : Array[MapTask[T]] = [Visit(self)]
  let results : Array[Term[U]] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(Value(value)) => results.push(Value(f(value)))
      Visit(Variable(name)) => results.push(Variable(name))
      Visit(Apply(head, arguments)) => {
        tasks.push(BuildApply(arguments.length()))
        for i = arguments.length() - 1; i >= 0; i = i - 1 {
          tasks.push(Visit(arguments[i]))
        }
        tasks.push(Visit(head))
      }
      Visit(Bind(name, body)) => {
        tasks.push(BuildBind(name))
        tasks.push(Visit(body))
      }
      BuildApply(arity) => {
        let base = results.length() - arity
        let arguments = Array::makei(arity, fn(i) { results[base + i] })
        let head = results[base - 1]
        results.truncate(base - 1)
        results.push(Apply(head, arguments))
      }
      BuildBind(name) => {
        let body = results[results.length() - 1]
        results[results.length() - 1] = Bind(name, body)
      }
    }
  }
  results[0]
}

///|
/// Renames free occurrences. A binder shadows a source name of the renaming.
pub fn[T] Term::rename_free(
  self : Term[T],
  renaming : @core.Renaming,
) -> Term[T] {
  rebuild(
    self,
    renaming,
    fn(_, name, renaming) { Variable(renaming.apply(name)) },
    fn(name, body, renaming) {
      let under_binder = renaming.without(name)
      if under_binder.targets().contains(name) {
        // the binder would capture a renamed variable: freshen it first
        let used = all_names(body).union(under_binder.support()).add(name)
        let fresh = @core.fresh_name(name, used)
        let renamed_body = generic_rename_bound_visit(body, true, name, fresh)
        (fresh, renamed_body, under_binder)
      } else {
        (name, body, under_binder)
      }
    },
  )
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
    Some(generic_rename_bound_visit(self, true, from, to_))
  }
}
