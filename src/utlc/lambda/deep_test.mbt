// Deep terms (issue #13): the rules and the normalizer use a constant host
// stack depth in the nesting depth of the term. The checks below walk the
// results with loops instead of `==` or `Debug`, which are recursive.

///|
const DEPTH : Int = 100_000

///|
/// `Bind(x, next)` nested `depth` times around `leaf`, for distinct binder
/// names `x0`, `x1`, ...
fn deep_binders(depth : Int, leaf : @syntax.Term[Int]) -> @syntax.Term[Int] {
  let mut term = leaf
  for level = depth - 1; level >= 0; level = level - 1 {
    term = Bind(@core.Name::new("x" + level.to_string()), term)
  }
  term
}

///|
/// The body under `depth` binders, found with a loop.
fn under_binders(depth : Int, term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  let mut current = term
  for _ in 0..<depth {
    match current {
      Bind(_, body) => current = body
      _ => return None
    }
  }
  Some(current)
}

///|
test "deep terms: beta reads through deep empty applications" {
  // `Apply(Apply(...Apply(λx. x, [])..., []), [a])` is a redex
  let x = @core.Name::new("x")
  let mut head : @syntax.Term[Int] = Bind(x, Variable(x))
  for _ in 0..<DEPTH {
    head = Apply(head, [])
  }
  match @lambda.beta_rule(Apply(head, [Value(4)])) {
    Some(Value(4)) => ()
    _ => fail("the redex behind the empty applications was not reduced")
  }
  assert_true(@lambda.beta_rule(Apply(head, [])) is None)
}

///|
test "deep terms: eta checks a deep function for the bound variable" {
  // `λx. F x` with `F = f (f (... (f y)))` nested `DEPTH` times
  let x = @core.Name::new("x")
  let f = @core.Name::new("f")
  let y = @core.Name::new("y")
  let mut function : @syntax.Term[Int] = Variable(y)
  for _ in 0..<DEPTH {
    function = Apply(Variable(f), [function])
  }
  let eta_redex : @syntax.Term[Int] = Bind(x, Apply(function, [Variable(x)]))
  match @lambda.eta_rule(eta_redex) {
    Some(reduced) => assert_true(physical_equal(reduced, function))
    None => fail("the eta redex was not reduced")
  }
  // the bound variable occurring at the bottom of `F` blocks the step
  let mut capturing : @syntax.Term[Int] = Variable(x)
  for _ in 0..<DEPTH {
    capturing = Apply(Variable(f), [capturing])
  }
  assert_true(
    @lambda.eta_rule(Bind(x, Apply(capturing, [Variable(x)]))) is None,
  )
  // so does it under deep empty applications around the body
  let mut body : @syntax.Term[Int] = Apply(capturing, [Variable(x)])
  for _ in 0..<DEPTH {
    body = Apply(body, [])
  }
  assert_true(@lambda.eta_rule(Bind(x, body)) is None)
  // but a binder of `x` inside `F` hides the occurrence
  assert_true(
    @lambda.eta_rule(Bind(x, Apply(Bind(x, capturing), [Variable(x)])))
    is Some(Bind(_, _)),
  )
}

///|
test "deep terms: normalize contracts a redex under deep binders" {
  // `λx0. ... λx(DEPTH-1). (λy. y) c` reduces in one step to
  // `λx0. ... λx(DEPTH-1). c`
  let y = @core.Name::new("y")
  let c = @core.Name::new("c")
  let redex : @syntax.Term[Int] = Apply(Bind(y, Variable(y)), [Variable(c)])
  match @lambda.normalize(deep_binders(DEPTH, redex), 10) {
    NormalForm(term~, steps=1) =>
      assert_true(
        under_binders(DEPTH, term) is Some(Variable(name)) && name == c,
      )
    _ => fail("expected a normal form after one step")
  }
}

///|
test "deep terms: normalize contracts a redex deep in argument position" {
  // `f (f (... ((λy. y) c)))` reduces in one step to `f (f (... c))`
  let f = @core.Name::new("f")
  let y = @core.Name::new("y")
  let c = @core.Name::new("c")
  let mut term : @syntax.Term[Int] = Apply(Bind(y, Variable(y)), [Variable(c)])
  for _ in 0..<DEPTH {
    term = Apply(Variable(f), [term])
  }
  match @lambda.normalize(term, 10) {
    NormalForm(term=normal, steps=1) => {
      let mut current = normal
      for _ in 0..<DEPTH {
        match current {
          Apply(Variable(_), [argument]) => current = argument
          _ => fail("the spine changed")
        }
      }
      assert_true(current is Variable(name) && name == c)
    }
    _ => fail("expected a normal form after one step")
  }
}
