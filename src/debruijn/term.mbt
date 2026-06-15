///|
/// Lambda syntax with bound variables represented by De Bruijn indices.
pub(all) enum DbTerm[T] {
  Value(T)
  Free(@core.Name)
  Bound(Int)
  Apply(DbTerm[T], Array[DbTerm[T]])
  Bind(DbTerm[T])
} derive(Eq, Debug)

///|
/// Scope and index failures in De Bruijn operations.
pub(all) enum ScopeError {
  UnboundIndex(index~ : Int, depth~ : Int)
  NegativeIndex(index~ : Int)
  NegativeShift(index~ : Int, delta~ : Int, cutoff~ : Int)
} derive(Eq, Debug)

///|
fn lookup_bound(name : @core.Name, binders : Array[@core.Name]) -> Int? {
  for i = binders.length() - 1; i >= 0; i = i - 1 {
    if binders[i] == name {
      return Some(binders.length() - i - 1)
    }
  }
  None
}

///|
fn[T] from_named_visit(
  term : @syntax.Term[T],
  binders : Array[@core.Name],
) -> DbTerm[T] {
  match term {
    Value(value) => Value(value)
    Variable(name) =>
      match lookup_bound(name, binders) {
        Some(index) => Bound(index)
        None => Free(name)
      }
    Apply(head, arguments) =>
      Apply(
        from_named_visit(head, binders),
        arguments.map(fn(argument) { from_named_visit(argument, binders) }),
      )
    Bind(name, body) => {
      let next_binders = binders.copy()
      next_binders.push(name)
      Bind(from_named_visit(body, next_binders))
    }
  }
}

///|
/// Converts named syntax to De Bruijn syntax. Free names remain named.
pub fn[T] from_named(term : @syntax.Term[T]) -> DbTerm[T] {
  from_named_visit(term, [])
}

///|
fn[T] collect_free_names(term : DbTerm[T]) -> @hashset.HashSet[@core.Name] {
  match term {
    Value(_) | Bound(_) => @hashset.new()
    Free(name) => @hashset.from_array([name])
    Apply(head, arguments) => {
      let mut result = collect_free_names(head)
      for argument in arguments {
        result = result.union(collect_free_names(argument))
      }
      result
    }
    Bind(body) => collect_free_names(body)
  }
}

///|
fn[T] to_named_visit(
  term : DbTerm[T],
  binders : Array[@core.Name],
  used : @hashset.HashSet[@core.Name],
) -> Result[@syntax.Term[T], ScopeError] {
  match term {
    Value(value) => Ok(Value(value))
    Free(name) => Ok(Variable(name))
    Bound(index) => {
      if index < 0 {
        return Err(NegativeIndex(index~))
      }
      if index >= binders.length() {
        return Err(UnboundIndex(index~, depth=binders.length()))
      }
      Ok(Variable(binders[binders.length() - index - 1]))
    }
    Apply(head, arguments) =>
      match to_named_visit(head, binders, used) {
        Err(error) => Err(error)
        Ok(named_head) => {
          let named_arguments : Array[@syntax.Term[T]] = []
          for argument in arguments {
            match to_named_visit(argument, binders, used) {
              Err(error) => return Err(error)
              Ok(named_argument) => named_arguments.push(named_argument)
            }
          }
          Ok(Apply(named_head, named_arguments))
        }
      }
    Bind(body) => {
      let hint = @core.Name::new("x")
      let fresh = @core.fresh_name(hint, used)
      let next_binders = binders.copy()
      next_binders.push(fresh)
      match to_named_visit(body, next_binders, used.add(fresh)) {
        Ok(named_body) => Ok(Bind(fresh, named_body))
        Err(error) => Err(error)
      }
    }
  }
}

///|
/// Converts a well-scoped De Bruijn term to deterministic named syntax.
pub fn[T] to_named(term : DbTerm[T]) -> Result[@syntax.Term[T], ScopeError] {
  to_named_visit(term, [], collect_free_names(term))
}

///|
fn[T] validate_visit(term : DbTerm[T], depth : Int) -> Result[Unit, ScopeError] {
  match term {
    Value(_) | Free(_) => Ok(())
    Bound(index) =>
      if index < 0 {
        Err(NegativeIndex(index~))
      } else if index >= depth {
        Err(UnboundIndex(index~, depth~))
      } else {
        Ok(())
      }
    Apply(head, arguments) =>
      match validate_visit(head, depth) {
        Err(error) => Err(error)
        Ok(_) => {
          for argument in arguments {
            match validate_visit(argument, depth) {
              Err(error) => return Err(error)
              Ok(_) => continue
            }
          }
          Ok(())
        }
      }
    Bind(body) => validate_visit(body, depth + 1)
  }
}

///|
/// Validates that every bound index refers to an enclosing binder.
pub fn[T] validate(term : DbTerm[T]) -> Result[Unit, ScopeError] {
  validate_visit(term, 0)
}

///|
fn[T] shift_visit(
  term : DbTerm[T],
  delta : Int,
  cutoff : Int,
  depth : Int,
) -> Result[DbTerm[T], ScopeError] {
  match term {
    Value(value) => Ok(Value(value))
    Free(name) => Ok(Free(name))
    Bound(index) => {
      if index < 0 {
        return Err(NegativeIndex(index~))
      }
      if index >= cutoff + depth {
        let shifted = index + delta
        if shifted < 0 {
          Err(NegativeShift(index~, delta~, cutoff=cutoff + depth))
        } else {
          Ok(Bound(shifted))
        }
      } else {
        Ok(Bound(index))
      }
    }
    Apply(head, arguments) =>
      match shift_visit(head, delta, cutoff, depth) {
        Err(error) => Err(error)
        Ok(next_head) => {
          let next_arguments : Array[DbTerm[T]] = []
          for argument in arguments {
            match shift_visit(argument, delta, cutoff, depth) {
              Err(error) => return Err(error)
              Ok(next_argument) => next_arguments.push(next_argument)
            }
          }
          Ok(Apply(next_head, next_arguments))
        }
      }
    Bind(body) =>
      match shift_visit(body, delta, cutoff, depth + 1) {
        Ok(next_body) => Ok(Bind(next_body))
        Err(error) => Err(error)
      }
  }
}

///|
/// Shifts free bound indices `>= cutoff` by `delta`.
pub fn[T] shift(
  term : DbTerm[T],
  delta : Int,
  cutoff : Int,
) -> Result[DbTerm[T], ScopeError] {
  shift_visit(term, delta, cutoff, 0)
}

///|
fn[T] substitute_visit(
  term : DbTerm[T],
  index : Int,
  replacement : DbTerm[T],
  depth : Int,
) -> Result[DbTerm[T], ScopeError] {
  match term {
    Value(value) => Ok(Value(value))
    Free(name) => Ok(Free(name))
    Bound(current) => {
      if current < 0 {
        return Err(NegativeIndex(index=current))
      }
      if current == index + depth {
        shift(replacement, depth, 0)
      } else {
        Ok(Bound(current))
      }
    }
    Apply(head, arguments) =>
      match substitute_visit(head, index, replacement, depth) {
        Err(error) => Err(error)
        Ok(next_head) => {
          let next_arguments : Array[DbTerm[T]] = []
          for argument in arguments {
            match substitute_visit(argument, index, replacement, depth) {
              Err(error) => return Err(error)
              Ok(next_argument) => next_arguments.push(next_argument)
            }
          }
          Ok(Apply(next_head, next_arguments))
        }
      }
    Bind(body) =>
      match substitute_visit(body, index, replacement, depth + 1) {
        Ok(next_body) => Ok(Bind(next_body))
        Err(error) => Err(error)
      }
  }
}

///|
/// Replaces the bound index relative to the current term root.
pub fn[T] substitute_bound(
  term : DbTerm[T],
  index : Int,
  replacement : DbTerm[T],
) -> Result[DbTerm[T], ScopeError] {
  if index < 0 {
    Err(NegativeIndex(index~))
  } else {
    substitute_visit(term, index, replacement, 0)
  }
}

///|
/// Opens one binder body with an argument using standard De Bruijn shifts.
pub fn[T] instantiate(
  body : DbTerm[T],
  argument : DbTerm[T],
) -> Result[DbTerm[T], ScopeError] {
  match shift(argument, 1, 0) {
    Err(error) => Err(error)
    Ok(lifted_argument) =>
      match substitute_bound(body, 0, lifted_argument) {
        Err(error) => Err(error)
        Ok(substituted) => shift(substituted, -1, 0)
      }
  }
}
