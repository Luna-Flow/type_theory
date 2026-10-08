///|
test "named round trip preserves alpha equivalence" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let named : @syntax.Term[Int] = @syntax.Bind(
    x,
    @syntax.Apply(@syntax.Variable(x), [@syntax.Variable(y)]),
  )
  match @debruijn.to_named(@debruijn.from_named(named)) {
    Ok(round_trip) => assert_true(@syntax.alpha_equal(named, round_trip))
    Err(_) => assert_false(true)
  }
}

///|
test "well scoped debruijn round trip is exact" {
  let free = @core.Name::new("free")
  let term : @debruijn.DbTerm[String] = Bind(
    Apply(Bound(0), [Free(free), Bind(Bound(1)), Value("atom")]),
  )
  match @debruijn.to_named(term) {
    Err(_) => assert_false(true)
    Ok(named) => assert_true(@debruijn.from_named(named) == term)
  }
}

///|
test "scope validation rejects dangling indices" {
  let term : @debruijn.DbTerm[Int] = Bind(Bound(1))
  assert_true(@debruijn.validate(term) == Err(UnboundIndex(index=1, depth=1)))
}

///|
test "binder instantiation uses standard shifting" {
  let body : @debruijn.DbTerm[Int] = Bind(Apply(Bound(1), [Bound(0)]))
  let argument : @debruijn.DbTerm[Int] = Free(@core.Name::new("y"))
  assert_true(
    @debruijn.instantiate(body, argument) ==
    Ok(Bind(Apply(Free(@core.Name::new("y")), [Bound(0)]))),
  )
}

///|
test "single step records the beta redex path" {
  let redex : @debruijn.DbTerm[Int] = Apply(Bind(Bound(0)), [Value(7)])
  let term : @debruijn.DbTerm[Int] = Bind(
    Apply(Free(@core.Name::new("f")), [redex]),
  )
  match @debruijn.reduce_once(term) {
    Reduced(after~, rule~, path~, ..) => {
      assert_true(after == Bind(Apply(Free(@core.Name::new("f")), [Value(7)])))
      assert_true(rule.value() == "beta")
      assert_true(path.to_array() == [BinderBody, ApplyArgument(0)])
    }
    _ => assert_false(true)
  }
}
