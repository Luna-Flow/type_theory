///|
test "beta reduction substitutes generic values without capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let function : @syntax.Term[Int] = abstraction(
    x,
    abstraction(y, application(@syntax.Variable(x), @syntax.Variable(y))),
  )
  let term = application(function, @syntax.Variable(y))
  let expected : @syntax.Term[Int] = abstraction(
    @core.Name::new("y_1"),
    application(@syntax.Variable(y), @syntax.Variable(@core.Name::new("y_1"))),
  )
  assert_true(beta_rule(term) == Some(expected))
  assert_true(
    normalize(term, 10) == NormalForm(term=@syntax.Variable(y), steps=2),
  )
}

///|
test "beta reduction preserves wrapped domain values" {
  let x = @core.Name::new("x")
  let identity : @syntax.Term[String] = abstraction(x, @syntax.Variable(x))
  assert_true(
    normalize(application(identity, @syntax.Value("payload")), 2) ==
    NormalForm(term=@syntax.Value("payload"), steps=1),
  )
}

///|
test "named and debruijn beta reduction agree modulo alpha" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let named : @syntax.Term[Int] = application(
    abstraction(
      x,
      abstraction(y, application(@syntax.Variable(x), @syntax.Variable(y))),
    ),
    @syntax.Variable(y),
  )
  match (beta_rule(named), @debruijn.reduce_once(@debruijn.from_named(named))) {
    (Some(named_after), @debruijn.Reduced(after=db_after, ..)) =>
      match @debruijn.to_named(db_after) {
        Ok(db_named_after) =>
          assert_true(@syntax.alpha_equal(named_after, db_named_after))
        Err(_) => assert_false(true)
      }
    _ => assert_false(true)
  }
}
