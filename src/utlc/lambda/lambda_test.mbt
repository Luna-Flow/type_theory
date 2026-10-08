///|
test "beta reduction substitutes generic values without capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let function : @syntax.Term[Int] = @lambda.abstraction(
    x,
    @lambda.abstraction(
      y,
      @lambda.application(@syntax.Variable(x), @syntax.Variable(y)),
    ),
  )
  let term = @lambda.application(function, @syntax.Variable(y))
  let expected : @syntax.Term[Int] = @lambda.abstraction(
    @core.Name::new("y_1"),
    @lambda.application(
      @syntax.Variable(y),
      @syntax.Variable(@core.Name::new("y_1")),
    ),
  )
  assert_true(@lambda.beta_rule(term) == Some(expected))
  assert_true(
    @lambda.normalize(term, 10) == NormalForm(term=@syntax.Variable(y), steps=2),
  )
}

///|
test "beta reduction preserves wrapped domain values" {
  let x = @core.Name::new("x")
  let identity : @syntax.Term[String] = @lambda.abstraction(
    x,
    @syntax.Variable(x),
  )
  assert_true(
    @lambda.normalize(
      @lambda.application(identity, @syntax.Value("payload")),
      2,
    ) ==
    NormalForm(term=@syntax.Value("payload"), steps=1),
  )
}

///|
test "named and debruijn beta reduction agree modulo alpha" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let named : @syntax.Term[Int] = @lambda.application(
    @lambda.abstraction(
      x,
      @lambda.abstraction(
        y,
        @lambda.application(@syntax.Variable(x), @syntax.Variable(y)),
      ),
    ),
    @syntax.Variable(y),
  )
  match
    (
      @lambda.beta_rule(named),
      @debruijn.reduce_once(@debruijn.from_named(named)),
    ) {
    (Some(named_after), @debruijn.Reduced(after=db_after, ..)) =>
      match @debruijn.to_named(db_after) {
        Ok(db_named_after) =>
          assert_true(@syntax.alpha_equal(named_after, db_named_after))
        Err(_) => assert_false(true)
      }
    _ => assert_false(true)
  }
}

///|
test "empty applications are read as their head" {
  // issue #2
  let x = @core.Name::new("x")
  let a = @core.Name::new("a")
  let f = @core.Name::new("f")
  let identity : @syntax.Term[Int] = @syntax.Bind(x, @syntax.Variable(x))
  let hidden : @syntax.Term[Int] = @syntax.Apply(@syntax.Apply(identity, []), [
    @syntax.Variable(a),
  ])
  assert_true(@lambda.beta_rule(hidden) == Some(@syntax.Variable(a)))
  assert_true(
    @lambda.normalize(hidden, 10) ==
    NormalForm(term=@syntax.Variable(a), steps=1),
  )
  assert_true(@lambda.beta_rule(@syntax.Apply(identity, [])) is None)
  // weak head reduction finds the redex at the root as well
  assert_true(
    @eval.reduce_once(
      hidden,
      @rewrite.RuleName::unsafe_new("beta"),
      @lambda.beta_rule,
      WeakHead,
    )
    is Reduced(after=Variable(_), ..),
  )
  // λx. (f (x)) with the argument and the body wrapped in empty applications
  let wrapped : @syntax.Term[Int] = @syntax.Bind(
    x,
    @syntax.Apply(
      @syntax.Apply(@syntax.Variable(f), [
        @syntax.Apply(@syntax.Variable(x), []),
      ]),
      [],
    ),
  )
  assert_true(@lambda.eta_rule(wrapped) == Some(@syntax.Variable(f)))
}
