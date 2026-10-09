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
  // validation comes before any step: the redex before the bad index is not
  // contracted (issue #16)
  assert_true(
    @debruijn.normalize(elsewhere, 10) ==
    ScopeFailure(term=elsewhere, error=UnboundIndex(index=0, depth=0), steps=0),
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

///|
test "downward shift rejects capture by an enclosing binder" {
  // issue #9
  let f = @core.Name::new("f")
  // λ. (free 0): the free variable must not become the parameter
  let under_binder : @debruijn.DbTerm[Int] = Bind(Bound(1))
  assert_true(
    @debruijn.shift(under_binder, -1, 0) ==
    Err(NegativeShift(index=1, delta=-1, cutoff=1)),
  )
  // a free index at the cutoff must not drop below it
  let at_cutoff : @debruijn.DbTerm[Int] = Bound(1)
  assert_true(
    @debruijn.shift(at_cutoff, -1, 1) ==
    Err(NegativeShift(index=1, delta=-1, cutoff=1)),
  )
  // deeper binders and a larger delta
  let deep : @debruijn.DbTerm[Int] = Bind(Bind(Bound(3)))
  assert_true(
    @debruijn.shift(deep, -2, 0) ==
    Err(NegativeShift(index=3, delta=-2, cutoff=2)),
  )
  let deep_cutoff : @debruijn.DbTerm[Int] = Bind(Bound(3))
  assert_true(
    @debruijn.shift(deep_cutoff, -2, 2) ==
    Err(NegativeShift(index=3, delta=-2, cutoff=3)),
  )
  // the capture is found inside an application spine
  let spine : @debruijn.DbTerm[Int] = Apply(Free(f), [Bound(2), Bind(Bound(1))])
  assert_true(
    @debruijn.shift(spine, -1, 0) ==
    Err(NegativeShift(index=1, delta=-1, cutoff=1)),
  )
  let head : @debruijn.DbTerm[Int] = Apply(Bind(Apply(Bound(0), [Bound(1)])), [
    Value(1),
  ])
  assert_true(
    @debruijn.shift(head, -1, 0) ==
    Err(NegativeShift(index=1, delta=-1, cutoff=1)),
  )
  // a shift below zero is still rejected
  let top : @debruijn.DbTerm[Int] = Bound(0)
  assert_true(
    @debruijn.shift(top, -1, 0) ==
    Err(NegativeShift(index=0, delta=-1, cutoff=0)),
  )
}

///|
test "downward shift keeps free indices at or above the cutoff" {
  // issue #9: i + d == c is the boundary that must succeed
  let f = @core.Name::new("f")
  let under_binder : @debruijn.DbTerm[Int] = Bind(Bound(2))
  assert_true(@debruijn.shift(under_binder, -1, 0) == Ok(Bind(Bound(1))))
  let at_cutoff : @debruijn.DbTerm[Int] = Bound(2)
  assert_true(@debruijn.shift(at_cutoff, -1, 1) == Ok(Bound(1)))
  let deep : @debruijn.DbTerm[Int] = Bind(Bind(Apply(Bound(4), [Bound(1)])))
  assert_true(
    @debruijn.shift(deep, -2, 0) == Ok(Bind(Bind(Apply(Bound(2), [Bound(1)])))),
  )
  let spine : @debruijn.DbTerm[Int] = Apply(Free(f), [
    Bound(1),
    Bind(Apply(Bound(0), [Bound(2)])),
  ])
  assert_true(
    @debruijn.shift(spine, -1, 0) ==
    Ok(Apply(Free(f), [Bound(0), Bind(Apply(Bound(0), [Bound(1)]))])),
  )
  // indices bound inside the term are untouched by any delta
  let closed : @debruijn.DbTerm[Int] = Bind(Bind(Apply(Bound(1), [Bound(0)])))
  assert_true(@debruijn.shift(closed, -5, 0) == Ok(closed))
}

///|
test "upward shift is unchanged" {
  let open_term : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(1)]))
  assert_true(
    @debruijn.shift(open_term, 2, 0) == Ok(Bind(Apply(Bound(0), [Bound(3)]))),
  )
  let below : @debruijn.DbTerm[Int] = Apply(Bound(0), [Bound(1)])
  assert_true(@debruijn.shift(below, 1, 1) == Ok(Apply(Bound(0), [Bound(2)])))
  let deep : @debruijn.DbTerm[Int] = Bind(Bind(Bound(2)))
  assert_true(@debruijn.shift(deep, 3, 0) == Ok(Bind(Bind(Bound(5)))))
  assert_true(@debruijn.shift(deep, 0, 0) == Ok(deep))
}
