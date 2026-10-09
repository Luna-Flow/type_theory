// Terms nested to depth 100_000 (issue #13). Every operation keeps its
// pending work in a heap array, so these run on every backend; with host
// recursion they overflowed the js, wasm and wasm-gc stacks.

///|
const DEPTH : Int = 100_000

///|
/// `f (f (... (f 0)))`: nested in argument position.
fn argument_chain(
  depth : Int,
  leaf : @debruijn.DbTerm[Int],
) -> @debruijn.DbTerm[Int] {
  let f = @core.Name::new("f")
  let mut term = leaf
  for _ in 0..<depth {
    term = Apply(Free(f), [term])
  }
  term
}

///|
/// `((leaf 0) 1) ... (depth - 1)`: nested in head position.
fn head_chain(
  depth : Int,
  leaf : @debruijn.DbTerm[Int],
) -> @debruijn.DbTerm[Int] {
  let mut term = leaf
  for i in 0..<depth {
    term = Apply(term, [Value(i)])
  }
  term
}

///|
/// `λ. λ. ... λ. body` with `depth` binders.
fn bind_chain(
  depth : Int,
  body : @debruijn.DbTerm[Int],
) -> @debruijn.DbTerm[Int] {
  let mut term = body
  for _ in 0..<depth {
    term = Bind(term)
  }
  term
}

///|
/// A beta-normal mixture of binders, heads and arguments around `leaf`, with
/// indices that reach far out. Level `i` (counted from the inside) adds
/// `i % 3` binders, so `leaf` is under `MIXTURE_BINDERS` binders when `depth`
/// is `DEPTH`, and level `i` is under at least `reach(depth, i)` binders
/// added by the levels outside it.
fn mixture_with(
  depth : Int,
  leaf : @debruijn.DbTerm[Int],
) -> @debruijn.DbTerm[Int] {
  let f = @core.Name::new("f")
  let mut term = leaf
  for i in 0..<depth {
    let outside = reach(depth, i)
    term = match i % 3 {
      // nested in argument position, under no new binder
      0 => {
        let head : @debruijn.DbTerm[Int] = if outside > 0 {
          Bound(i * 7 % outside)
        } else {
          Value(i)
        }
        Apply(head, [term, Value(i)])
      }
      // nested in head position (the previous level is an application)
      1 => Bind(Apply(Apply(term, [Free(f)]), [Bound(i * 7 % (outside + 1))]))
      // nested in argument position under two binders
      _ =>
        Bind(
          Apply(Free(f), [Bound(i * 5 % (outside + 1)), Bind(term), Bound(0)]),
        )
    }
  }
  term
}

///|
/// A lower bound for the number of binders that the levels after level `i`
/// of `mixture_with(depth, _)` add: at least two of three levels add one.
fn reach(depth : Int, i : Int) -> Int {
  2 * (depth - 1 - i) / 3
}

///|
/// The depth of the deepest redex. `@rewrite.ReductionPath::prepend` copies
/// the path, so a path of length `n` costs O(n^2) to build.
const PATH_DEPTH : Int = 5_000

///|
const MIXTURE_BINDERS : Int = 99_999

///|
/// A well-scoped, beta-normal mixture whose innermost leaf refers to the
/// outermost binder.
fn mixture(depth : Int) -> @debruijn.DbTerm[Int] {
  mixture_with(depth, Bound(MIXTURE_BINDERS - 1))
}

///|
test "validate deep terms" {
  assert_true(@debruijn.validate(argument_chain(DEPTH, Value(0))) == Ok(()))
  assert_true(@debruijn.validate(head_chain(DEPTH, Value(0))) == Ok(()))
  assert_true(@debruijn.validate(bind_chain(DEPTH, Bound(DEPTH - 1))) == Ok(()))
  assert_true(@debruijn.validate(mixture(DEPTH)) == Ok(()))
  assert_true(
    @debruijn.validate(bind_chain(DEPTH, Bound(DEPTH))) ==
    Err(UnboundIndex(index=DEPTH, depth=DEPTH)),
  )
  // the first error in pre-order is reported: the one at the bottom of the
  // deep head, not the later argument
  let bad_head = head_chain(DEPTH, Bound(-1))
  assert_true(
    @debruijn.validate(Apply(bad_head, [Bound(3)])) ==
    Err(NegativeIndex(index=-1)),
  )
  let bad_argument = argument_chain(DEPTH, Bound(2))
  assert_true(
    @debruijn.validate(Apply(Bound(-4), [bad_argument])) ==
    Err(NegativeIndex(index=-4)),
  )
  assert_true(
    @debruijn.validate(Apply(Value(0), [bad_argument, Bound(-4)])) ==
    Err(UnboundIndex(index=2, depth=0)),
  )
}

///|
test "equality of deep terms" {
  assert_true(
    argument_chain(DEPTH, Value(0)) == argument_chain(DEPTH, Value(0)),
  )
  assert_true(
    argument_chain(DEPTH, Value(0)) != argument_chain(DEPTH, Value(1)),
  )
  assert_true(head_chain(DEPTH, Value(0)) == head_chain(DEPTH, Value(0)))
  assert_true(head_chain(DEPTH, Value(0)) != head_chain(DEPTH, Value(1)))
  assert_true(bind_chain(DEPTH, Bound(0)) == bind_chain(DEPTH, Bound(0)))
  assert_true(bind_chain(DEPTH, Bound(0)) != bind_chain(DEPTH - 1, Bound(0)))
  assert_true(mixture(DEPTH) == mixture(DEPTH))
  assert_true(mixture(DEPTH) != mixture(DEPTH - 1))
}

///|
test "from_named and to_named on deep terms" {
  let f = @core.Name::new("f")
  let x = @core.Name::new("x")
  // nested in argument position
  let mut named : @syntax.Term[Int] = Variable(x)
  for _ in 0..<DEPTH {
    named = Apply(Variable(f), [named])
  }
  let expected = argument_chain(DEPTH, Free(x))
  assert_true(@debruijn.from_named(named) == expected)
  // nested in head position
  named = Variable(x)
  for i in 0..<DEPTH {
    named = Apply(named, [Value(i)])
  }
  assert_true(@debruijn.from_named(named) == head_chain(DEPTH, Free(x)))
  // binders with distinct names: the innermost body refers to the outermost
  let outermost = @core.Name::new("v0")
  named = Apply(Variable(outermost), [Variable(f)])
  for i in 0..<DEPTH {
    named = Bind(@core.Name::new("v" + (DEPTH - 1 - i).to_string()), named)
  }
  let nameless = @debruijn.from_named(named)
  assert_true(nameless == bind_chain(DEPTH, Apply(Bound(DEPTH - 1), [Free(f)])))
  // every binder shadows the previous one
  named = Variable(x)
  for _ in 0..<DEPTH {
    named = Bind(x, Apply(Variable(x), [named]))
  }
  let shadowed = @debruijn.from_named(named)
  let mut expected_shadowed : @debruijn.DbTerm[Int] = Bound(0)
  for _ in 0..<DEPTH {
    expected_shadowed = Bind(Apply(Bound(0), [expected_shadowed]))
  }
  assert_true(shadowed == expected_shadowed)
  // round trips through named syntax
  for
    term in [
      argument_chain(DEPTH, Value(0)),
      head_chain(DEPTH, Free(x)),
      nameless,
      shadowed,
      mixture(DEPTH),
    ] {
    match @debruijn.to_named(term) {
      Ok(back) => assert_true(@debruijn.from_named(back) == term)
      Err(_) => fail("well scoped")
    }
  }
  // binders are named x, x_1, x_2, ... avoiding the free name x
  match @debruijn.to_named(bind_chain(DEPTH, Apply(Free(x), [Bound(0)]))) {
    Ok(back) => {
      let mut current = back
      let mut level = 0
      while current is Bind(name, body) {
        assert_eq(name.text(), "x_" + (level + 1).to_string())
        current = body
        level = level + 1
      }
      assert_eq(level, DEPTH)
    }
    Err(_) => fail("well scoped")
  }
  assert_true(
    @debruijn.to_named(bind_chain(DEPTH, Bound(DEPTH + 2))) ==
    Err(UnboundIndex(index=DEPTH + 2, depth=DEPTH)),
  )
  assert_true(
    @debruijn.to_named(head_chain(DEPTH, Bound(-1))) ==
    Err(NegativeIndex(index=-1)),
  )
}

///|
test "shift deep terms" {
  assert_true(
    @debruijn.shift(bind_chain(DEPTH, Bound(DEPTH)), 3, 0) ==
    Ok(bind_chain(DEPTH, Bound(DEPTH + 3))),
  )
  assert_true(
    @debruijn.shift(bind_chain(DEPTH, Bound(DEPTH + 1)), -1, 0) ==
    Ok(bind_chain(DEPTH, Bound(DEPTH))),
  )
  assert_true(
    @debruijn.shift(bind_chain(DEPTH, Bound(DEPTH)), -1, 0) ==
    Err(NegativeShift(index=DEPTH, delta=-1, cutoff=DEPTH)),
  )
  assert_true(
    @debruijn.shift(argument_chain(DEPTH, Bound(4)), -2, 1) ==
    Ok(argument_chain(DEPTH, Bound(2))),
  )
  assert_true(
    @debruijn.shift(head_chain(DEPTH, Bound(0)), 5, 0) ==
    Ok(head_chain(DEPTH, Bound(5))),
  )
  // indices bound inside the term are untouched
  assert_true(@debruijn.shift(mixture(DEPTH), 7, 0) == Ok(mixture(DEPTH)))
  assert_true(
    @debruijn.shift(head_chain(DEPTH, Bound(-1)), 1, 0) ==
    Err(NegativeIndex(index=-1)),
  )
}

///|
test "substitute and instantiate in deep terms" {
  let y = @core.Name::new("y")
  // the replacement is shifted under every binder it passes
  assert_true(
    @debruijn.substitute_bound(bind_chain(DEPTH, Bound(DEPTH)), 0, Bound(1)) ==
    Ok(bind_chain(DEPTH, Bound(DEPTH + 1))),
  )
  assert_true(
    @debruijn.substitute_bound(argument_chain(DEPTH, Bound(0)), 0, Free(y)) ==
    Ok(argument_chain(DEPTH, Free(y))),
  )
  assert_true(
    @debruijn.substitute_bound(head_chain(DEPTH, Bound(1)), 1, Free(y)) ==
    Ok(head_chain(DEPTH, Free(y))),
  )
  assert_true(
    @debruijn.substitute_bound(head_chain(DEPTH, Bound(-2)), 1, Free(y)) ==
    Err(NegativeIndex(index=-2)),
  )
  // a deep replacement
  assert_true(
    @debruijn.substitute_bound(
      Bind(Bound(1)),
      0,
      argument_chain(DEPTH, Bound(0)),
    ) ==
    Ok(Bind(argument_chain(DEPTH, Bound(1)))),
  )
  let body = bind_chain(DEPTH, Apply(Bound(DEPTH), [Bound(0)]))
  assert_true(
    @debruijn.instantiate(body, Free(y)) ==
    Ok(bind_chain(DEPTH, Apply(Free(y), [Bound(0)]))),
  )
  assert_true(
    @debruijn.instantiate(Bound(0), mixture(DEPTH)) == Ok(mixture(DEPTH)),
  )
}

///|
test "one step on deep terms" {
  let f = @core.Name::new("f")
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  // the search goes through a deep normal subterm before the redex
  let term : @debruijn.DbTerm[Int] = Apply(Free(f), [
    mixture(DEPTH),
    Apply(identity, [Value(1)]),
  ])
  match @debruijn.reduce_once(term) {
    Reduced(before~, after~, path~, ..) => {
      assert_true(before == term)
      assert_true(after == Apply(Free(f), [mixture(DEPTH), Value(1)]))
      assert_true(path.to_array() == [ApplyArgument(1)])
    }
    _ => fail("expected a step")
  }
  // a redex at the root with a deep body and a deep argument
  let redex : @debruijn.DbTerm[Int] = Apply(
    Bind(bind_chain(DEPTH, Apply(Bound(DEPTH), [Bound(0)]))),
    [argument_chain(DEPTH, Value(0))],
  )
  match @debruijn.reduce_once(redex) {
    Reduced(after~, path~, ..) => {
      assert_true(
        after ==
        bind_chain(DEPTH, Apply(argument_chain(DEPTH, Value(0)), [Bound(0)])),
      )
      assert_true(path.to_array() == [])
    }
    _ => fail("expected a step")
  }
  // normal forms
  assert_true(@debruijn.reduce_once(mixture(DEPTH)) == NoStep)
  assert_true(@debruijn.reduce_once(head_chain(DEPTH, Free(f))) == NoStep)
  assert_true(@debruijn.reduce_once(argument_chain(DEPTH, Value(0))) == NoStep)
  // ill-scoped input is reported before any step
  assert_true(
    @debruijn.reduce_once(Apply(identity, [bind_chain(DEPTH, Bound(DEPTH))])) ==
    ScopeFailure(UnboundIndex(index=DEPTH, depth=DEPTH)),
  )
}

///|
test "one step at the bottom of a deep term" {
  // the redex lies under PATH_DEPTH application heads and binders; the
  // reduction path has one frame per level
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  let deep_redex = bind_chain(
    PATH_DEPTH,
    head_chain(PATH_DEPTH, Apply(identity, [Value(-1)])),
  )
  match @debruijn.reduce_once(deep_redex) {
    Reduced(after~, path~, ..) => {
      assert_true(
        after == bind_chain(PATH_DEPTH, head_chain(PATH_DEPTH, Value(-1))),
      )
      assert_eq(path.length(), 2 * PATH_DEPTH)
    }
    _ => fail("expected a step")
  }
}

///|
test "normalize deep terms" {
  let f = @core.Name::new("f")
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  // one step to a deep normal form
  let term : @debruijn.DbTerm[Int] = Apply(
    Bind(bind_chain(DEPTH, Apply(Bound(DEPTH), [Bound(0)]))),
    [Free(f)],
  )
  assert_true(
    @debruijn.normalize(term, 10) ==
    NormalForm(term=bind_chain(DEPTH, Apply(Free(f), [Bound(0)])), steps=1),
  )
  // a deep normal form is returned unchanged
  assert_true(
    @debruijn.normalize(mixture(DEPTH), 10) ==
    NormalForm(term=mixture(DEPTH), steps=0),
  )
  // a few redexes beside a deep normal subterm
  let spine : @debruijn.DbTerm[Int] = Apply(Free(f), [
    argument_chain(DEPTH, Value(0)),
    Apply(identity, [Apply(identity, [Value(1)])]),
  ])
  assert_true(
    @debruijn.normalize(spine, 10) ==
    NormalForm(
      term=Apply(Free(f), [argument_chain(DEPTH, Value(0)), Value(1)]),
      steps=2,
    ),
  )
  assert_true(
    @debruijn.normalize(spine, 1) ==
    StepLimitReached(
      term=Apply(Free(f), [
        argument_chain(DEPTH, Value(0)),
        Apply(identity, [Value(1)]),
      ]),
      steps=1,
    ),
  )
  let bad : @debruijn.DbTerm[Int] = Apply(identity, [
    mixture_with(DEPTH, Bound(2 * DEPTH)),
  ])
  assert_true(
    @debruijn.normalize(bad, 10) ==
    ScopeFailure(
      term=bad,
      error=UnboundIndex(index=2 * DEPTH, depth=MIXTURE_BINDERS),
      steps=0,
    ),
  )
}
