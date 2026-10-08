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

///|
test "empty applications are read as their head" {
  // issue #2
  let a = @core.Name::new("a")
  let hidden : @debruijn.DbTerm[Int] = Apply(Apply(Bind(Bound(0)), []), [
    Free(a),
  ])
  match @debruijn.reduce_once(hidden) {
    Reduced(after~, path~, ..) => {
      assert_true(after == Free(a))
      assert_true(path.to_array() == [])
    }
    _ => assert_false(true)
  }
  let spine : @debruijn.DbTerm[Int] = Apply(
    Apply(Apply(Bind(Bind(Bound(1))), []), []),
    [Value(1), Value(2)],
  )
  assert_true(
    @debruijn.normalize(spine, 10) == NormalForm(term=Value(1), steps=2),
  )
  // an empty application of a binder alone is not a redex
  let lone : @debruijn.DbTerm[Int] = Apply(Bind(Bound(0)), [])
  assert_true(@debruijn.reduce_once(lone) == NoStep)
}

///|
test "reducers report ill-scoped input" {
  // issue #3
  let negative : @debruijn.DbTerm[Int] = Bind(Bound(-1))
  assert_true(
    @debruijn.reduce_once(negative) == ScopeFailure(NegativeIndex(index=-1)),
  )
  assert_true(
    @debruijn.normalize(negative, 10) ==
    ScopeFailure(term=negative, error=NegativeIndex(index=-1), steps=0),
  )
  let dangling : @debruijn.DbTerm[Int] = Apply(Bind(Bound(5)), [Value(1)])
  assert_true(
    @debruijn.reduce_once(dangling) ==
    ScopeFailure(UnboundIndex(index=5, depth=1)),
  )
  assert_true(
    @debruijn.normalize(dangling, 10) ==
    ScopeFailure(term=dangling, error=UnboundIndex(index=5, depth=1), steps=0),
  )
  // a bad index away from every redex is reported too
  let elsewhere : @debruijn.DbTerm[Int] = Apply(Free(@core.Name::new("f")), [
    Apply(Bind(Bound(0)), [Value(1)]),
    Bound(0),
  ])
  assert_true(
    @debruijn.reduce_once(elsewhere) ==
    ScopeFailure(UnboundIndex(index=0, depth=0)),
  )
  // a well-scoped term with redexes under binders still reduces
  let under : @debruijn.DbTerm[Int] = Bind(
    Apply(Bind(Apply(Bound(1), [Bound(0)])), [Value(2)]),
  )
  assert_true(
    @debruijn.normalize(under, 10) ==
    NormalForm(term=Bind(Apply(Bound(0), [Value(2)])), steps=1),
  )
}
