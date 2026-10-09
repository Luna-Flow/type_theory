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
  match @nbe.normalize(term, 200) {
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
  match @nbe.normalize(term, 100) {
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
  assert_true(@nbe.normalize(omega, 40) is FuelExhausted(_))
}

///|
test "quote converts neutral levels back to indices" {
  let identity : @debruijn.DbTerm[String] = Bind(Bound(0))
  match @nbe.normalize(identity, 40) {
    NormalForm(term=normal, ..) => assert_true(normal == identity)
    _ => assert_false(true)
  }
}

///|
test "public eval reflect and quote expose the semantic pipeline" {
  let free = @core.Name::new("free")
  let reflected : @nbe.Semantic[Unit] = @nbe.reflect_free(free)
  match @nbe.quote(reflected, 0, 10) {
    @nbe.QuoteResult::Quoted(term~, ..) =>
      assert_true(term == @debruijn.Free(free))
    _ => assert_false(true)
  }
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  match @nbe.eval(identity, 20) {
    Evaluated(value~, ..) =>
      match @nbe.quote(value, 0, 20) {
        @nbe.QuoteResult::Quoted(term~, ..) => assert_true(term == identity)
        _ => assert_false(true)
      }
    _ => assert_false(true)
  }
}

///|
test "nbe and small step agree on empty applications" {
  // (λ. 0) a with the head wrapped in an empty application (issue #2)
  let a = @core.Name::new("a")
  let term : @debruijn.DbTerm[Int] = Apply(Apply(Bind(Bound(0)), []), [Free(a)])
  assert_true(
    @debruijn.normalize(term, 10) == @debruijn.NormalForm(term=Free(a), steps=1),
  )
  match @nbe.normalize(term, 100) {
    NormalForm(term=normal, ..) => assert_true(normal == Free(a))
    _ => assert_false(true)
  }
}

///|
test "omega exhausts a large budget without growing the stack" {
  // (λ. 0 0) (λ. 0 0) with a budget of thirty million units (issue #12)
  let omega_function : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0)]))
  let omega : @debruijn.DbTerm[Int] = @debruijn.Apply(omega_function, [
    omega_function,
  ])
  assert_true(
    @nbe.normalize(omega, 30_000_000) == FuelExhausted(consumed=30_000_000),
  )
}

///|
test "a growing divergent application exhausts a large budget" {
  // (λ. 0 0 0) (λ. 0 0 0) reduces to ((w w) w) w ...: the head grows
  let w : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0), Bound(0)]))
  let term : @debruijn.DbTerm[Int] = Apply(w, [w])
  assert_true(
    @nbe.normalize(term, 30_000_000) == FuelExhausted(consumed=30_000_000),
  )
}

///|
test "readback of an unbounded normal form exhausts a large budget" {
  // (λ. f (0 0)) (λ. f (0 0)) has the infinite normal form f (f (f ...))
  let f = @core.Name::new("f")
  let w : @debruijn.DbTerm[Int] = Bind(
    Apply(Free(f), [Apply(Bound(0), [Bound(0)])]),
  )
  let spine : @debruijn.DbTerm[Int] = Apply(w, [w])
  assert_true(
    @nbe.normalize(spine, 30_000_000) == FuelExhausted(consumed=30_000_000),
  )
  // (λ. λ. 1 1) (λ. λ. 1 1) has the infinite normal form λ. λ. λ. ...
  let v : @debruijn.DbTerm[Int] = Bind(Bind(Apply(Bound(1), [Bound(1)])))
  let binders : @debruijn.DbTerm[Int] = Apply(v, [v])
  assert_true(
    @nbe.normalize(binders, 30_000_000) == FuelExhausted(consumed=30_000_000),
  )
}

///|
test "fuel accounting is exact and reproducible" {
  // Church numerals: 2 2 = 4, 2 2 2 = 16, and 2 2 f a = f (f (f (f a)))
  let f = @core.Name::new("f")
  let a = @core.Name::new("a")
  let two : @debruijn.DbTerm[Int] = Bind(
    Bind(Apply(Bound(1), [Apply(Bound(1), [Bound(0)])])),
  )
  let cases : Array[(@debruijn.DbTerm[Int], Int)] = [
    (Apply(two, [two]), 82),
    (Apply(two, [two, two]), 473),
    (Apply(two, [two, Free(f), Free(a)]), 85),
  ]
  for case in cases {
    let (term, expected) = case
    match @nbe.normalize(term, 100_000) {
      NormalForm(consumed~, ..) as result => {
        assert_eq(consumed, expected)
        assert_true(@nbe.normalize(term, consumed) == result)
        assert_true(
          @nbe.normalize(term, consumed - 1) ==
          FuelExhausted(consumed=consumed - 1),
        )
      }
      _ => fail("Church numeral arithmetic normalizes")
    }
  }
  match @nbe.normalize(Apply(two, [two, Free(f), Free(a)]), 100) {
    NormalForm(term~, ..) => {
      let mut expected : @debruijn.DbTerm[Int] = Free(a)
      for _ in 0..<4 {
        expected = Apply(Free(f), [expected])
      }
      assert_true(term == expected)
    }
    _ => fail("2 2 f a normalizes")
  }
}
