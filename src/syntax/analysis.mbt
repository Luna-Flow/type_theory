///|
fn[T] free_variables_visit(
  term : Term[T],
  bound : @hashset.HashSet[@core.Name],
) -> @hashset.HashSet[@core.Name] {
  match term {
    Value(_) => @hashset.new()
    Variable(name) =>
      if bound.contains(name) {
        @hashset.new()
      } else {
        @hashset.from_array([name])
      }
    Apply(head, arguments) => {
      let mut result = free_variables_visit(head, bound)
      for argument in arguments {
        result = result.union(free_variables_visit(argument, bound))
      }
      result
    }
    Bind(name, body) => free_variables_visit(body, bound.add(name))
  }
}

///|
/// Returns the free variables of a term.
pub fn[T] free_variables(term : Term[T]) -> @hashset.HashSet[@core.Name] {
  free_variables_visit(term, @hashset.new())
}

///|
/// Returns every free, bound, and binder name occurring in a term.
pub fn[T] all_names(term : Term[T]) -> @hashset.HashSet[@core.Name] {
  match term {
    Value(_) => @hashset.new()
    Variable(name) => @hashset.from_array([name])
    Apply(head, arguments) => {
      let mut result = all_names(head)
      for argument in arguments {
        result = result.union(all_names(argument))
      }
      result
    }
    Bind(name, body) => all_names(body).add(name)
  }
}

///|
fn lookup_binding(
  name : @core.Name,
  environment : Array[(@core.Name, Int)],
) -> Int? {
  for i = environment.length() - 1; i >= 0; i = i - 1 {
    if environment[i].0 == name {
      return Some(environment[i].1)
    }
  }
  None
}

///|
fn[T : Eq] alpha_equal_visit(
  left : Term[T],
  right : Term[T],
  left_env : Array[(@core.Name, Int)],
  right_env : Array[(@core.Name, Int)],
  depth : Int,
) -> Bool {
  match (left, right) {
    (Value(a), Value(b)) => a == b
    (Variable(a), Variable(b)) =>
      match (lookup_binding(a, left_env), lookup_binding(b, right_env)) {
        (Some(left_depth), Some(right_depth)) => left_depth == right_depth
        (None, None) => a == b
        _ => false
      }
    (Apply(left_head, left_args), Apply(right_head, right_args)) => {
      if left_args.length() != right_args.length() ||
        !alpha_equal_visit(left_head, right_head, left_env, right_env, depth) {
        return false
      }
      for i in 0..<left_args.length() {
        if !alpha_equal_visit(
            left_args[i],
            right_args[i],
            left_env,
            right_env,
            depth,
          ) {
          return false
        }
      }
      true
    }
    (Bind(left_name, left_body), Bind(right_name, right_body)) => {
      let next_left = left_env.copy()
      let next_right = right_env.copy()
      next_left.push((left_name, depth))
      next_right.push((right_name, depth))
      alpha_equal_visit(left_body, right_body, next_left, next_right, depth + 1)
    }
    _ => false
  }
}

///|
/// Alpha-equivalence compares values and free names literally, and binders by scope.
pub fn[T : Eq] alpha_equal(left : Term[T], right : Term[T]) -> Bool {
  alpha_equal_visit(left, right, [], [], 0)
}
