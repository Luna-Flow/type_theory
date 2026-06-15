///|
test "generic values map independently of syntax" {
  let x = @core.Name::new("x")
  let term : Term[Int] = Apply(Value(2), [Variable(x), Value(3)])
  assert_true(
    term.map_values(fn(value) { value.to_string() }) ==
    Apply(Value("2"), [Variable(x), Value("3")]),
  )
}

///|
test "free variables and alpha equivalence respect nested binders" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let left : Term[Int] = Bind(x, Apply(Variable(x), [Variable(z)]))
  let right : Term[Int] = Bind(y, Apply(Variable(y), [Variable(z)]))
  assert_true(free_variables(left).contains(z))
  assert_false(free_variables(left).contains(x))
  assert_true(alpha_equal(left, right))
}

///|
test "free renaming avoids capture under a binder" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let term : Term[Int] = Bind(y, Variable(x))
  let renamed = term.rename_free(@core.Renaming::singleton(x, y))
  let expected : Term[Int] = Bind(@core.Name::new("y_1"), Variable(y))
  assert_true(renamed == expected)
  assert_true(free_variables(renamed).contains(y))
}

///|
test "checked alpha renaming rejects a capturing target" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let body : Term[Int] = Bind(y, Variable(x))
  assert_true(body.alpha_rename_bound(x, y) is None)
  assert_true(body.alpha_rename_bound(x, z) == Some(Bind(y, Variable(z))))
}

///|
test "alpha equivalence is reflexive for generated atoms" {
  fn property(value : Int) -> Bool {
    let x = @core.Name::new("x")
    let term : Term[Int] = Term::Bind(
      x,
      Term::Apply(Term::Variable(x), [Term::Value(value)]),
    )
    alpha_equal(term, term)
  }
  @qc.quick_check_fn(property)
}
