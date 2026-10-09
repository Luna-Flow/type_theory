// Input terms nested to depth 100_000 (issue #13). Validation, evaluation
// and readback keep their pending work in heap arrays, so these run on every
// backend; with host recursion they overflowed the js, wasm and wasm-gc
// stacks.

///|
const DEPTH : Int = 100_000

///|
/// Enough fuel for the terms below, which need a few units per node.
const FUEL : Int = 100 * DEPTH

///|
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
fn normal_form(term : @debruijn.DbTerm[Int]) -> @debruijn.DbTerm[Int]? {
  match @nbe.normalize(term, FUEL) {
    NormalForm(term~, ..) => Some(term)
    _ => None
  }
}

///|
test "nbe of deep normal terms" {
  let x = @core.Name::new("x")
  let terms = [
    argument_chain(DEPTH, Value(0)),
    head_chain(DEPTH, Free(x)),
    bind_chain(DEPTH, Bound(DEPTH - 1)),
    bind_chain(DEPTH, Apply(Bound(0), [Bound(DEPTH - 1)])),
    // binders inside arguments, arguments inside binders
    argument_chain(DEPTH, bind_chain(DEPTH, head_chain(DEPTH, Bound(7)))),
  ]
  for term in terms {
    assert_true(normal_form(term) == Some(term))
  }
}

///|
test "eval and quote deep terms" {
  let term = bind_chain(DEPTH, argument_chain(DEPTH, Bound(DEPTH - 1)))
  match @nbe.eval(term, FUEL) {
    Evaluated(value~, ..) =>
      match @nbe.quote(value, 0, FUEL) {
        Quoted(term=quoted, ..) => assert_true(quoted == term)
        _ => fail("quote of a normal term")
      }
    _ => fail("evaluation of a normal term")
  }
  // a deep neutral read back under some binders
  match @nbe.eval(head_chain(DEPTH, Free(@core.Name::new("g"))), FUEL) {
    Evaluated(value~, ..) =>
      match @nbe.quote(value, 3, FUEL) {
        Quoted(term=quoted, ..) =>
          assert_true(quoted == head_chain(DEPTH, Free(@core.Name::new("g"))))
        _ => fail("quote of a neutral")
      }
    _ => fail("evaluation of a neutral")
  }
}

///|
test "nbe of deep terms with redexes" {
  let f = @core.Name::new("f")
  let identity : @debruijn.DbTerm[Int] = Bind(Bound(0))
  // (λ. 0) ((λ. 0) (... ((λ. 0) 7)))
  assert_true(normal_form(argument_chain_of(identity, DEPTH)) == Some(Value(7)))
  // f ((λ. 0) (f ((λ. 0) (... 7))))
  let mut alternating : @debruijn.DbTerm[Int] = Value(7)
  for _ in 0..<DEPTH {
    alternating = Apply(Free(f), [Apply(identity, [alternating])])
  }
  assert_true(normal_form(alternating) == Some(argument_chain(DEPTH, Value(7))))
  // a redex at the bottom of a deep binder chain refers to the outermost
  // binder
  assert_true(
    normal_form(bind_chain(DEPTH, Apply(identity, [Bound(DEPTH - 1)]))) ==
    Some(bind_chain(DEPTH, Bound(DEPTH - 1))),
  )
  // a deep head chain whose head is a binder chain: every argument is
  // consumed by one binder
  let consumer = bind_chain(DEPTH, Bound(DEPTH - 1))
  assert_true(normal_form(head_chain(DEPTH, consumer)) == Some(Value(0)))
}

///|
/// `(λ. 0) ((λ. 0) (... ((λ. 0) 7)))` with `depth` applications of `function`.
fn argument_chain_of(
  function : @debruijn.DbTerm[Int],
  depth : Int,
) -> @debruijn.DbTerm[Int] {
  let mut term : @debruijn.DbTerm[Int] = Value(7)
  for _ in 0..<depth {
    term = Apply(function, [term])
  }
  term
}

///|
test "nbe rejects deep ill-scoped terms" {
  assert_true(
    @nbe.normalize(bind_chain(DEPTH, Bound(DEPTH)), FUEL) ==
    ScopeFailure(error=UnboundIndex(index=DEPTH, depth=DEPTH), consumed=0),
  )
  assert_true(
    @nbe.eval(head_chain(DEPTH, Bound(-1)), FUEL)
    is ScopeFailure(error=NegativeIndex(index=-1), consumed=0),
  )
}
