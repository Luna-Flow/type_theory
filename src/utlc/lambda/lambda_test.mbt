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

///|
/// Erases every empty application `Apply(h, [])` to `h`.
fn erase_empty_applications(term : @syntax.Term[Int]) -> @syntax.Term[Int] {
  match term {
    Apply(head, []) => erase_empty_applications(head)
    Apply(head, arguments) =>
      Apply(
        erase_empty_applications(head),
        arguments.map(erase_empty_applications),
      )
    Bind(name, body) => Bind(name, erase_empty_applications(body))
    _ => term
  }
}

///|
test "beta then eta agrees with normalize modulo empty applications" {
  // issue #16: λz. (λy. y) (z ())
  let z = @core.Name::new("z")
  let y = @core.Name::new("y")
  let term : @syntax.Term[Int] = Bind(
    z,
    Apply(Bind(y, Variable(y)), [Apply(Variable(z), [])]),
  )
  let beta = @rewrite.RuleName::unsafe_new("beta")
  let eta = @rewrite.RuleName::unsafe_new("eta")
  let beta_normal = match
    @eval.evaluate(term, beta, @lambda.beta_rule, NormalOrder, 10) {
    NormalForm(term~, ..) => term
    StepLimitReached(..) => fail("beta normal form")
  }
  let beta_eta = match
    @eval.evaluate(beta_normal, eta, @lambda.eta_rule, NormalOrder, 10) {
    NormalForm(term~, ..) => term
    StepLimitReached(..) => fail("eta normal form")
  }
  let normalized = match @lambda.normalize(term, 10) {
    NormalForm(term~, ..) => term
    StepLimitReached(..) => fail("beta-eta normal form")
  }
  // beta leaves λz. z (), which eta cannot contract; normalize contracts the
  // eta redex at the root first and returns λy. y
  assert_true(beta_eta == Bind(z, Apply(Variable(z), [])))
  assert_true(normalized == Bind(y, Variable(y)))
  assert_false(@syntax.alpha_equal(beta_eta, normalized))
  assert_true(
    @syntax.alpha_equal(
      erase_empty_applications(beta_eta),
      erase_empty_applications(normalized),
    ),
  )
}

///|
/// Rewrites every n-ary application `Apply(f, [a1, ..., an])` with `n > 0`
/// into the nested unary spine `Apply(...Apply(f, [a1])..., [an])`. Empty
/// applications are kept as they are.
fn curry(term : @syntax.Term[Int]) -> @syntax.Term[Int] {
  match term {
    Value(_) | Variable(_) => term
    Bind(name, body) => Bind(name, curry(body))
    Apply(head, []) => Apply(curry(head), [])
    Apply(head, arguments) =>
      arguments.fold(init=curry(head), fn(spine, argument) {
        Apply(spine, [curry(argument)])
      })
  }
}

///|
test "applicative order picks the same redex for n-ary and curried spines" {
  // issue #11
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let v = @core.Name::new("v")
  let k : @syntax.Term[Int] = Bind(x, Bind(y, Variable(y)))
  let inner : @syntax.Term[Int] = Apply(Bind(y, Variable(y)), [Variable(v)])
  let nary : @syntax.Term[Int] = Apply(k, [Value(0), inner])
  let nested : @syntax.Term[Int] = Apply(Apply(k, [Value(0)]), [inner])
  let beta = @rewrite.RuleName::unsafe_new("beta")
  // (λx. λy. y) 0 is contracted first in both encodings
  let expected : @syntax.Term[Int] = Apply(Bind(y, Variable(y)), [inner])
  match @eval.reduce_once(nary, beta, @lambda.beta_rule, ApplicativeOrder) {
    Reduced(before~, after~, path~, ..) => {
      assert_true(before == nary)
      assert_true(after == expected)
      assert_true(path.to_array() == [])
    }
    NoStep => assert_false(true)
  }
  match @eval.reduce_once(nested, beta, @lambda.beta_rule, ApplicativeOrder) {
    Reduced(after~, path~, ..) => {
      assert_true(after == expected)
      assert_true(path.to_array() == [@rewrite.ApplyHead])
    }
    NoStep => assert_false(true)
  }
  // the generic n-ary traversal keeps plain post-order on the n-ary tree
  match @rewrite.bottom_up_once(nary, beta, @lambda.beta_rule) {
    Reduced(path~, ..) =>
      assert_true(path.to_array() == [@rewrite.ApplyArgument(1)])
    NoStep => assert_false(true)
  }
}

///|
/// A deterministic linear congruential generator for the property tests.
priv struct Lcg {
  mut state : UInt64
}

///|
fn Lcg::below(self : Lcg, bound : Int) -> Int {
  self.state = self.state * 6364136223846793005UL + 1442695040888963407UL
  ((self.state >> 33) % bound.to_uint64()).to_int()
}

///|
fn random_name(rng : Lcg) -> @core.Name {
  @core.Name::new(["x", "y", "z"][rng.below(3)])
}

///|
/// A random term with few names (to force renaming), many redexes and n-ary
/// spines of length 0 to 3.
fn random_term(rng : Lcg, depth : Int) -> @syntax.Term[Int] {
  let choice = if depth <= 0 { rng.below(3) } else { rng.below(7) }
  match choice {
    0 => Value(rng.below(3))
    1 | 2 => Variable(random_name(rng))
    3 | 4 => Bind(random_name(rng), random_term(rng, depth - 1))
    _ => {
      let head : @syntax.Term[Int] = if rng.below(2) == 0 {
        Bind(random_name(rng), random_term(rng, depth - 1))
      } else {
        random_term(rng, depth - 1)
      }
      let count = [0, 1, 2, 2, 3, 3][rng.below(6)]
      let arguments = Array::makei(count, fn(_) { random_term(rng, depth - 1) })
      Apply(head, arguments)
    }
  }
}

///|
/// Runs `strategy` for up to `max_steps` steps on `term` and on its curried
/// form in lockstep, and reports whether every step corresponds.
fn same_steps_when_curried(
  term : @syntax.Term[Int],
  strategy : @eval.Strategy,
  max_steps : Int,
) -> Bool {
  let beta = @rewrite.RuleName::unsafe_new("beta")
  let mut nary = term
  let mut curried = curry(term)
  for _ in 0..<max_steps {
    match
      (
        @eval.reduce_once(nary, beta, @lambda.beta_rule, strategy),
        @eval.reduce_once(curried, beta, @lambda.beta_rule, strategy),
      ) {
      (NoStep, NoStep) => return true
      (Reduced(after=nary_after, ..), Reduced(after=curried_after, ..)) => {
        if !@syntax.alpha_equal(curry(nary_after), curried_after) {
          return false
        }
        nary = nary_after
        curried = curried_after
      }
      _ => return false
    }
  }
  true
}

///|
test "every strategy takes the same steps on a term and its curried form" {
  // issue #11
  let rng = Lcg::{ state: 11, }
  let strategies : Array[@eval.Strategy] = [
    NormalOrder,
    ApplicativeOrder,
    WeakHead,
    FullNormal,
  ]
  let mismatches = strategies.map(fn(_) { 0 })
  for _ in 0..<1000 {
    let term = random_term(rng, 4)
    for i, strategy in strategies {
      if !same_steps_when_curried(term, strategy, 6) {
        mismatches[i] = mismatches[i] + 1
      }
    }
  }
  assert_eq(mismatches, [0, 0, 0, 0])
}
