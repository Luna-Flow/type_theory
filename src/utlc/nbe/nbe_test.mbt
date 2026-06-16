///|
test "nbe agrees with small step on normalizing terms" {
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Apply(Bound(0), [Value(1)])), [
    Bind(Bound(0)),
  ])
  let expected : @debruijn.DbTerm[Int] = Value(1)
  assert_true(
    @debruijn.normalize(term, 20) ==
    @debruijn.NormalForm(term=expected, steps=2),
  )
  match normalize(term, 200) {
    NormalForm(term=normal, ..) => assert_true(normal == expected)
    _ => assert_false(true)
  }
}

///|
test "lazy nbe does not force an unused divergent argument" {
  let omega_function : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0)]))
  let omega : @debruijn.DbTerm[Int] = @debruijn.Apply(omega_function, [
    omega_function,
  ])
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Value(7)), [omega])
  match normalize(term, 100) {
    NormalForm(term=normal, ..) => assert_true(normal == Value(7))
    _ => assert_false(true)
  }
}

///|
test "omega exhausts fuel instead of hanging" {
  let omega_function : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0)]))
  let omega : @debruijn.DbTerm[Int] = @debruijn.Apply(omega_function, [
    omega_function,
  ])
  assert_true(normalize(omega, 40) is FuelExhausted(_))
}

///|
test "quote converts neutral levels back to indices" {
  let identity : @debruijn.DbTerm[String] = Bind(Bound(0))
  match normalize(identity, 40) {
    NormalForm(term=normal, ..) => assert_true(normal == identity)
    _ => assert_false(true)
  }
}

///|
test "public eval reflect and quote expose the semantic pipeline" {
  let free = @core.Name::new("free")
  let reflected : Semantic[Unit] = reflect_free(free)
  match quote(reflected, 0, 10) {
    QuoteResult::Quoted(term~, ..) => assert_true(term == @debruijn.Free(free))
    _ => assert_false(true)
  }
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  match eval(identity, 20) {
    Evaluated(value~, ..) =>
      match quote(value, 0, 20) {
        QuoteResult::Quoted(term~, ..) => assert_true(term == identity)
        _ => assert_false(true)
      }
    _ => assert_false(true)
  }
}
