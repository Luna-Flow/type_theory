///|
/// Lambda syntax with bound variables represented by De Bruijn indices.
///
/// Terms are shared, not copied. Treat the argument array of `Apply` as
/// immutable; build a new term instead of changing it in place.
///
/// Equality (`==`) is structural and works on terms of any nesting depth;
/// the derived `Debug` recurses over the term.
pub(all) enum DbTerm[T] {
  Value(T)
  Free(@core.Name)
  Bound(Int)
  Apply(DbTerm[T], Array[DbTerm[T]])
  Bind(DbTerm[T])
} derive(Debug)

///|
/// Scope and index failures in De Bruijn operations.
pub(all) enum ScopeError {
  UnboundIndex(index~ : Int, depth~ : Int)
  NegativeIndex(index~ : Int)
  NegativeShift(index~ : Int, delta~ : Int, cutoff~ : Int)
  NegativeCutoff(cutoff~ : Int)
} derive(Eq, Debug)

// Bounded-stack traversals (issue #13).
//
// Every operation of this package is specified by structural recursion over
// the term (see the debruijn design page). Run as host recursion, such a
// definition needs one host stack frame per level of nesting, and the js,
// wasm and wasm-gc stacks overflow at a depth of a few thousand. The
// operations run instead as loops over an explicit stack of pending work in a
// heap `Array`:
//
// - a check (`validate`, `==`) pops the next subterm and pushes its children,
//   the head on top of the arguments in reverse order, so that subterms are
//   visited in pre-order from left to right, as the recursive definition
//   visits them;
// - a translation (`map_indices`, `from_named`, `to_named`) pushes, for a
//   node with children, a task that rebuilds the node below the visits of the
//   children; each visit leaves its result on a second stack, from which the
//   rebuild task takes them.
//
// Leaves are reached in the order of the recursive definition, and errors
// arise only at leaves, so the first error reported is the same one.

///|
/// Structural equality, the relation a derived `Eq` would compute. The pairs
/// still to compare are kept on a heap stack.
pub impl[T : Eq] Eq for DbTerm[T] with fn equal(self, other) {
  let pending : Array[(DbTerm[T], DbTerm[T])] = [(self, other)]
  while pending.pop() is Some((left, right)) {
    match (left, right) {
      (Value(a), Value(b)) => if a != b { return false }
      (Free(a), Free(b)) => if a != b { return false }
      (Bound(a), Bound(b)) => if a != b { return false }
      (Apply(left_head, left_arguments), Apply(right_head, right_arguments)) => {
        if left_arguments.length() != right_arguments.length() {
          return false
        }
        for i = left_arguments.length() - 1; i >= 0; i = i - 1 {
          pending.push((left_arguments[i], right_arguments[i]))
        }
        pending.push((left_head, right_head))
      }
      (Bind(left_body), Bind(right_body)) =>
        pending.push((left_body, right_body))
      _ => return false
    }
  }
  true
}

///|
/// A pending step of a translation of terms of type `S`.
priv enum Task[S, B] {
  /// Translate this subterm, which lies under this many binders.
  Visit(S, Int)
  /// Take the translations of a head and this many arguments and rebuild an
  /// application.
  BuildApply(Int)
  /// Take the translation of a body and rebuild a binder with this data.
  BuildBind(B)
}

///|
/// Pushes the rebuild task of an application and, above it, the visits of
/// its head and arguments, so that the head is translated first and the
/// arguments follow from left to right.
fn[S, B] push_application(
  tasks : Array[Task[S, B]],
  head : S,
  arguments : Array[S],
  depth : Int,
) -> Unit {
  tasks.push(BuildApply(arguments.length()))
  for i = arguments.length() - 1; i >= 0; i = i - 1 {
    tasks.push(Visit(arguments[i], depth))
  }
  tasks.push(Visit(head, depth))
}

///|
/// Takes the translations of a head and `count` arguments.
fn[R] pop_application(results : Array[R], count : Int) -> (R, Array[R]) {
  let arguments = results.drain(results.length() - count, results.length())
  (pop_result(results), arguments)
}

///|
fn[R] pop_result(results : Array[R]) -> R {
  match results.pop() {
    Some(result) => result
    None => abort("a rebuild task runs after the visits of its children")
  }
}

///|
/// Converts named syntax to De Bruijn syntax. Free names remain named.
pub fn[T] from_named(term : @syntax.Term[T]) -> DbTerm[T] {
  // for each name, the levels of the enclosing binders of that name,
  // innermost last
  let scopes : Map[@core.Name, Array[Int]] = Map([])
  let mut depth = 0
  let tasks : Array[Task[@syntax.Term[T], @core.Name]] = [Visit(term, 0)]
  let results : Array[DbTerm[T]] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(Value(value), _) => results.push(Value(value))
      Visit(Variable(name), _) =>
        match scopes.get(name) {
          // the nearest enclosing binder of `name`
          Some(levels) if levels.last() is Some(level) =>
            results.push(Bound(depth - level - 1))
          _ => results.push(Free(name))
        }
      Visit(Apply(head, arguments), _) =>
        push_application(tasks, head, arguments, depth)
      Visit(Bind(name, body), _) => {
        match scopes.get(name) {
          Some(levels) => levels.push(depth)
          None => scopes.set(name, [depth])
        }
        depth = depth + 1
        tasks.push(BuildBind(name))
        tasks.push(Visit(body, depth))
      }
      BuildApply(count) => {
        let (head, arguments) = pop_application(results, count)
        results.push(Apply(head, arguments))
      }
      BuildBind(name) => {
        // leave the scope of the binder
        depth = depth - 1
        if scopes.get(name) is Some(levels) {
          levels.pop() |> ignore
        }
        results.push(Bind(pop_result(results)))
      }
    }
  }
  pop_result(results)
}

///|
fn[T] collect_free_names(term : DbTerm[T]) -> Set[@core.Name] {
  let names : Set[@core.Name] = Set([])
  let pending = [term]
  while pending.pop() is Some(current) {
    match current {
      Value(_) | Bound(_) => ()
      Free(name) => names.add(name)
      Apply(head, arguments) => {
        pending.push(head)
        for argument in arguments {
          pending.push(argument)
        }
      }
      Bind(body) => pending.push(body)
    }
  }
  names
}

///|
/// Converts a well-scoped De Bruijn term to deterministic named syntax.
pub fn[T] to_named(term : DbTerm[T]) -> Result[@syntax.Term[T], ScopeError] {
  // A binder gets the first name of `x`, `x_1`, `x_2`, ... (the sequence of
  // `@core.fresh_name` for the hint `x`) that is neither a free name of the
  // term nor the name of an enclosing binder. By induction on the level, the
  // enclosing binders of a binder at level `n` have the first `n` names of
  // the sequence that are not free names, so the binder gets the next one:
  // the name depends only on the level, and is computed once in `names[n]`.
  let free_names = collect_free_names(term)
  let names : Array[@core.Name] = []
  let mut suffix = 0
  let tasks : Array[Task[DbTerm[T], @core.Name]] = [Visit(term, 0)]
  let results : Array[@syntax.Term[T]] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(Value(value), _) => results.push(Value(value))
      Visit(Free(name), _) => results.push(Variable(name))
      Visit(Bound(index), depth) => {
        if index < 0 {
          return Err(NegativeIndex(index~))
        }
        if index >= depth {
          return Err(UnboundIndex(index~, depth~))
        }
        results.push(Variable(names[depth - index - 1]))
      }
      Visit(Apply(head, arguments), depth) =>
        push_application(tasks, head, arguments, depth)
      Visit(Bind(body), depth) => {
        while names.length() <= depth {
          let candidate = if suffix == 0 {
            @core.Name::new("x")
          } else {
            @core.Name::new("x_" + suffix.to_string())
          }
          suffix = suffix + 1
          if !free_names.contains(candidate) {
            names.push(candidate)
          }
        }
        tasks.push(BuildBind(names[depth]))
        tasks.push(Visit(body, depth + 1))
      }
      BuildApply(count) => {
        let (head, arguments) = pop_application(results, count)
        results.push(Apply(head, arguments))
      }
      BuildBind(name) => results.push(Bind(name, pop_result(results)))
    }
  }
  Ok(pop_result(results))
}

///|
/// Validates that every bound index refers to an enclosing binder.
pub fn[T] validate(term : DbTerm[T]) -> Result[Unit, ScopeError] {
  let pending : Array[(DbTerm[T], Int)] = [(term, 0)]
  while pending.pop() is Some((current, depth)) {
    match current {
      Value(_) | Free(_) => ()
      Bound(index) =>
        if index < 0 {
          return Err(NegativeIndex(index~))
        } else if index >= depth {
          return Err(UnboundIndex(index~, depth~))
        }
      Apply(head, arguments) => {
        for i = arguments.length() - 1; i >= 0; i = i - 1 {
          pending.push((arguments[i], depth))
        }
        pending.push((head, depth))
      }
      Bind(body) => pending.push((body, depth + 1))
    }
  }
  Ok(())
}

///|
/// Rebuilds `term`, replacing every `Bound(index)` under `depth` binders by
/// `leaf(index, depth)`, and stops at the first error in pre-order. This is
/// the traversal of `shift` and `substitute_bound`.
fn[T] map_indices(
  term : DbTerm[T],
  leaf : (Int, Int) -> Result[DbTerm[T], ScopeError],
) -> Result[DbTerm[T], ScopeError] {
  let tasks : Array[Task[DbTerm[T], Unit]] = [Visit(term, 0)]
  let results : Array[DbTerm[T]] = []
  while tasks.pop() is Some(task) {
    match task {
      Visit(Value(value), _) => results.push(Value(value))
      Visit(Free(name), _) => results.push(Free(name))
      Visit(Bound(index), depth) =>
        match leaf(index, depth) {
          Ok(result) => results.push(result)
          Err(error) => return Err(error)
        }
      Visit(Apply(head, arguments), depth) =>
        push_application(tasks, head, arguments, depth)
      Visit(Bind(body), depth) => {
        tasks.push(BuildBind(()))
        tasks.push(Visit(body, depth + 1))
      }
      BuildApply(count) => {
        let (head, arguments) = pop_application(results, count)
        results.push(Apply(head, arguments))
      }
      BuildBind(_) => results.push(Bind(pop_result(results)))
    }
  }
  Ok(pop_result(results))
}

///|
/// Shifts free bound indices `>= cutoff` by `delta`. Requires
/// `cutoff >= 0` and fails with `NegativeCutoff` otherwise, whatever the term.
/// Fails with `NegativeShift` if a shifted index would fall below the cutoff.
pub fn[T] shift(
  term : DbTerm[T],
  delta : Int,
  cutoff : Int,
) -> Result[DbTerm[T], ScopeError] {
  // A negative cutoff would treat indices bound inside the term as free.
  if cutoff < 0 {
    return Err(NegativeCutoff(cutoff~))
  }
  map_indices(term, fn(index, depth) {
    if index < 0 {
      return Err(NegativeIndex(index~))
    }
    if index >= cutoff + depth {
      let shifted = index + delta
      // A free index must stay free: below `cutoff + depth` it would be
      // captured by an enclosing binder, and below zero it is invalid.
      if shifted < cutoff + depth || shifted < 0 {
        Err(NegativeShift(index~, delta~, cutoff=cutoff + depth))
      } else {
        Ok(Bound(shifted))
      }
    } else {
      Ok(Bound(index))
    }
  })
}

///|
/// Replaces the bound index relative to the current term root.
pub fn[T] substitute_bound(
  term : DbTerm[T],
  index : Int,
  replacement : DbTerm[T],
) -> Result[DbTerm[T], ScopeError] {
  if index < 0 {
    return Err(NegativeIndex(index~))
  }
  map_indices(term, fn(current, depth) {
    if current < 0 {
      return Err(NegativeIndex(index=current))
    }
    if current == index + depth {
      shift(replacement, depth, 0)
    } else {
      Ok(Bound(current))
    }
  })
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
