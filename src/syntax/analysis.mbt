// Bounded-stack traversal (issue #13).
//
// The operations of this package are specified as structural recursion over
// a term. Implemented as host recursion, a term nested `n` levels deep needs
// `n` host frames, and the js/wasm stacks overflow at a few thousand levels.
//
// Each traversal runs instead as one loop over a heap `Array` of pending
// work, so the host stack depth is constant and the heap holds `O(n)` items:
//
// - a fold (free variables, names, equality, alpha-equivalence) pushes the
//   children of a node with the context the recursive call would have
//   received (the bound names, the binder environments) and accumulates the
//   answer, or stops at the first mismatch;
// - a rebuild (renaming, substitution, `map_values`) also pushes a frame that
//   reassembles the node from the results of its children (see `rebuild`).
//
// Children are pushed in reverse, so they are visited head first and then
// left to right, the order of the recursive definition.

///|
/// Returns the free variables of a term.
pub fn[T] free_variables(term : Term[T]) -> @hashset.HashSet[@core.Name] {
  generic_free_variables(term)
}

///|
/// Returns every free, bound, and binder name occurring in a term.
pub fn[T] all_names(term : Term[T]) -> @hashset.HashSet[@core.Name] {
  generic_all_names(term)
}

///|
/// A pending comparison of `alpha_equal`: two subterms and the binder
/// environments in scope, which map a name to the depth of its innermost
/// binder.
priv struct AlphaTask[T] {
  left : Term[T]
  right : Term[T]
  left_env : @hashmap.HashMap[@core.Name, Int]
  right_env : @hashmap.HashMap[@core.Name, Int]
  depth : Int
}

///|
/// Alpha-equivalence compares free names literally, binders by scope, and
/// values with `T`'s `==`. It is an equivalence relation exactly when `T`'s
/// `==` is one; for example a `Double` NaN payload is not equal to itself.
pub fn[T : Eq] alpha_equal(left : Term[T], right : Term[T]) -> Bool {
  // A variable bound on both sides must be bound at the same depth; a name
  // bound on one side only is never equal to a free one. `add` replaces the
  // entry of a shadowed binder, so `get` returns the innermost binder.
  let pending : Array[AlphaTask[T]] = [
    {
      left,
      right,
      left_env: @hashmap.HashMap::new(),
      right_env: @hashmap.HashMap::new(),
      depth: 0,
    },
  ]
  while pending.pop() is Some({ left, right, left_env, right_env, depth, }) {
    match (left, right) {
      (Value(a), Value(b)) => if a != b { return false }
      (Variable(a), Variable(b)) =>
        match (left_env.get(a), right_env.get(b)) {
          (Some(left_depth), Some(right_depth)) =>
            if left_depth != right_depth {
              return false
            }
          (None, None) => if a != b { return false }
          _ => return false
        }
      (Apply(left_head, left_args), Apply(right_head, right_args)) => {
        if left_args.length() != right_args.length() {
          return false
        }
        for i = left_args.length() - 1; i >= 0; i = i - 1 {
          pending.push({
            left: left_args[i],
            right: right_args[i],
            left_env,
            right_env,
            depth,
          })
        }
        pending.push({
          left: left_head,
          right: right_head,
          left_env,
          right_env,
          depth,
        })
      }
      (Bind(left_name, left_body), Bind(right_name, right_body)) =>
        pending.push({
          left: left_body,
          right: right_body,
          left_env: left_env.add(left_name, depth),
          right_env: right_env.add(right_name, depth),
          depth: depth + 1,
        })
      _ => return false
    }
  }
  true
}
