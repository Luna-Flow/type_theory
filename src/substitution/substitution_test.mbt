///|
test "substitution accepts generic values and avoids capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let term : @syntax.Term[Int] = Bind(
    y,
    Apply(Variable(x), [Value(1), Variable(y)]),
  )
  let result = Substitution::singleton(x, Variable(y)).apply(term)
  let expected : @syntax.Term[Int] = Bind(
    @core.Name::new("y_1"),
    Apply(Variable(y), [Value(1), Variable(@core.Name::new("y_1"))]),
  )
  assert_true(result == expected)
}

///|
test "substitution composition agrees with sequential application" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let first : Substitution[Int] = Substitution::singleton(x, Variable(y))
  let second = Substitution::singleton(y, Value(42))
  let term : @syntax.Term[Int] = @syntax.Apply(@syntax.Variable(x), [
    @syntax.Variable(y),
  ])
  assert_true(first.then(second).apply(term) == second.apply(first.apply(term)))
}

///|
test "renaming embeds into substitution" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let substitution : Substitution[String] = from_renaming(
    [x],
    @core.Renaming::singleton(x, y),
  )
  assert_true(substitution.apply(@syntax.Variable(x)) == @syntax.Variable(y))
}

///|
test "freshening avoids names used only by nested binders" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let term : @syntax.Term[Int] = @syntax.Bind(
    y,
    @syntax.Bind(y1, @syntax.Variable(y)),
  )
  let result = Substitution::singleton(x, @syntax.Variable(y)).apply(
    @syntax.Apply(@syntax.Variable(x), [term]),
  )
  let expected : @syntax.Term[Int] = @syntax.Apply(@syntax.Variable(y), [term])
  assert_true(result == expected)
}

///|
test "capture avoidance skips a nested binder name during alpha conversion" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let term : @syntax.Term[Int] = @syntax.Bind(
    y,
    @syntax.Apply(@syntax.Variable(x), [@syntax.Bind(y1, @syntax.Variable(y))]),
  )
  let result = Substitution::singleton(x, @syntax.Variable(y)).apply(term)
  let expected : @syntax.Term[Int] = @syntax.Bind(
    @core.Name::new("y_2"),
    @syntax.Apply(@syntax.Variable(y), [
      @syntax.Bind(y1, @syntax.Variable(@core.Name::new("y_2"))),
    ]),
  )
  assert_true(result == expected)
}

///|
test "fresh binders avoid the substitution domain" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let y1 = @core.Name::new("y_1")
  let v = @core.Name::new("v")
  let substitution : Substitution[Int] = Substitution::singleton(
    x,
    @syntax.Variable(y),
  ).set(y1, @syntax.Variable(v))
  let term : @syntax.Term[Int] = @syntax.Bind(
    y,
    @syntax.Apply(@syntax.Variable(x), [@syntax.Variable(y)]),
  )
  let expected : @syntax.Term[Int] = @syntax.Bind(
    @core.Name::new("y_2"),
    @syntax.Apply(@syntax.Variable(y), [
      @syntax.Variable(@core.Name::new("y_2")),
    ]),
  )
  assert_true(substitution.apply(term) == expected)
}
