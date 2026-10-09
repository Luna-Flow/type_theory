// Deep terms and types (issue #13): checking, inference and normalization
// use a constant host stack depth in the nesting depth of terms and types.
// The checks below walk the results with loops instead of `==` on terms or
// `Debug`, which are recursive. `==` on `Ty` is written with a loop.

///|
const DEPTH : Int = 100_000

///|
/// `domain -> domain -> ... -> result` with `arrows` arrows.
fn deep_arrow(arrows : Int, domain : @stlc.Ty, result : @stlc.Ty) -> @stlc.Ty {
  let mut ty = result
  for _ in 0..<arrows {
    ty = Arrow(domain, ty)
  }
  ty
}

///|
/// The name of binder number `level`.
fn binder(level : Int) -> String {
  "x" + level.to_string()
}

///|
/// `λx0. λx1. ... λx(depth-1). body`.
fn deep_lambda(depth : Int, body : @stlc.Term) -> @stlc.Term {
  let mut term = body
  for level = depth - 1; level >= 0; level = level - 1 {
    term = lam(binder(level), term)
  }
  term
}

///|
/// The signature `c : A`, `d : A -> A`.
fn deep_signature() -> @stlc.Signature {
  @stlc.Signature::empty()
  .extend_with(@core.Name::new("c"), base("A"))
  .extend_with(@core.Name::new("d"), Arrow(base("A"), base("A")))
}

///|
test "deep types: equality and checking against a deep arrow" {
  let a = base("A")
  let b = base("B")
  let ty = deep_arrow(DEPTH, a, b)
  let same = deep_arrow(DEPTH, a, b)
  let other = deep_arrow(DEPTH, a, a)
  assert_true(ty == same)
  assert_true(ty != other)
  assert_true(ty != deep_arrow(DEPTH - 1, a, b))
  let f = @core.Name::new("f")
  let ctx = @stlc.TypeContext::empty().extend_with(f, ty)
  let sig = @stlc.Signature::empty()
  assert_true(@stlc.check(sig, ctx, tm_var("f"), same) is Ok(_))
  match @stlc.infer(sig, ctx, tm_var("f")) {
    Ok(inferred) => assert_true(physical_equal(inferred, ty))
    Err(_) => fail("the variable was not inferred")
  }
  match @stlc.check(sig, ctx, tm_var("f"), other) {
    Err(TypeMismatch(expected~, actual~)) =>
      assert_true(physical_equal(expected, other) && physical_equal(actual, ty))
    _ => fail("expected a type mismatch")
  }
}

///|
test "deep terms: a deep lambda checked against a deep arrow" {
  let a = base("A")
  let sig = deep_signature()
  let ctx = @stlc.TypeContext::empty()
  let ty = deep_arrow(DEPTH, a, a)
  assert_true(
    @stlc.check(sig, ctx, deep_lambda(DEPTH, tm_var("x0")), ty) is Ok(_),
  )
  // the errors at the bottom are the ones of the recursive checker
  match @stlc.check(sig, ctx, deep_lambda(DEPTH, con("e")), ty) {
    Err(UnknownConstant(name)) => assert_eq(name.text(), "e")
    _ => fail("expected an unknown constant")
  }
  match
    @stlc.check(
      sig,
      ctx,
      deep_lambda(DEPTH, tm_var("x0")),
      deep_arrow(DEPTH, a, base("B")),
    ) {
    Err(TypeMismatch(expected~, actual~)) =>
      assert_true(expected == base("B") && actual == a)
    _ => fail("expected a type mismatch")
  }
  // one binder too many meets the result type `A`
  match @stlc.check(sig, ctx, deep_lambda(DEPTH + 1, tm_var("x0")), ty) {
    Err(CannotInferLambda) => ()
    _ => fail("expected a lambda that cannot be inferred")
  }
  assert_true(
    @stlc.infer(sig, ctx, deep_lambda(DEPTH, tm_var("x0")))
    is Err(CannotInferLambda),
  )
}

///|
test "deep terms: long curried spines" {
  let a = base("A")
  let b = base("B")
  let sig = deep_signature()
  let ctx = @stlc.TypeContext::empty().extend_with(
    @core.Name::new("f"),
    deep_arrow(DEPTH, a, b),
  )
  let arguments = Array::make(DEPTH, con("c"))
  // flat: `Apply(f, [c, ..., c])`
  assert_true(@stlc.infer(sig, ctx, spine(tm_var("f"), arguments)) == Ok(b))
  // nested in head position: `Apply(...Apply(f, [c])..., [c])`
  let mut nested = tm_var("f")
  for _ in 0..<DEPTH {
    nested = app(nested, con("c"))
  }
  assert_true(@stlc.infer(sig, ctx, nested) == Ok(b))
  assert_true(@stlc.check(sig, ctx, nested, b) == Ok(()))
  // one argument too many
  assert_true(
    @stlc.infer(sig, ctx, app(nested, con("c"))) == Err(ExpectedFunction(b)),
  )
  // an empty application at the bottom of the head chain
  let mut empty_inside : @stlc.Term = @syntax.Apply(tm_var("f"), [])
  for _ in 0..<DEPTH {
    empty_inside = app(empty_inside, con("c"))
  }
  assert_true(@stlc.infer(sig, ctx, empty_inside) == Err(EmptyApplication))
}

///|
test "deep terms: nested arguments and nested redexes" {
  let a = base("A")
  let sig = deep_signature()
  let ctx = @stlc.TypeContext::empty()
  // `d (d (... c))`
  let mut arguments = con("c")
  for _ in 0..<DEPTH {
    arguments = app(con("d"), arguments)
  }
  assert_true(@stlc.infer(sig, ctx, arguments) == Ok(a))
  assert_true(@stlc.check(sig, ctx, arguments, a) == Ok(()))
  // `(λx. x) ((λx. x) (... c))`: redexes in argument position
  let mut in_arguments = con("c")
  for _ in 0..<DEPTH {
    in_arguments = app(lam("x", tm_var("x")), in_arguments)
  }
  assert_true(@stlc.infer(sig, ctx, in_arguments) == Ok(a))
  assert_true(@stlc.check(sig, ctx, in_arguments, a) == Ok(()))
  assert_true(
    @stlc.check(sig, ctx, in_arguments, base("B")) ==
    Err(TypeMismatch(expected=base("B"), actual=a)),
  )
  // `(λx. (λx. (... (λx. c) c ...) c) c)`: redexes in head position
  let mut in_bodies = con("c")
  for _ in 0..<DEPTH {
    in_bodies = app(lam("x", in_bodies), con("c"))
  }
  assert_true(@stlc.infer(sig, ctx, in_bodies) == Ok(a))
  assert_true(@stlc.check(sig, ctx, in_bodies, a) == Ok(()))
  // the first error in traversal order is reported: the argument of the
  // innermost redex is inferred before its body is looked at
  let mut failing = app(lam("x", con("e1")), con("e2"))
  for _ in 0..<DEPTH {
    failing = app(lam("x", failing), con("c"))
  }
  match @stlc.infer(sig, ctx, failing) {
    Err(UnknownConstant(name)) => assert_eq(name.text(), "e2")
    _ => fail("expected an unknown constant")
  }
}

///|
test "deep types: eta-long normal form of a variable of a deep arrow type" {
  // `f : A -> ... -> A -> B` normalizes to `λx. λx_1. ... f x x_1 ...`
  let a = base("A")
  let b = base("B")
  let ty = deep_arrow(DEPTH, a, b)
  let f = @core.Name::new("f")
  let ctx = @stlc.TypeContext::empty().extend_with(f, ty)
  let normal = match
    @stlc.normalize_eta_long(@stlc.Signature::empty(), ctx, tm_var("f"), ty) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  let names : Array[@core.Name] = []
  let mut current = normal
  for _ in 0..<DEPTH {
    match current {
      @syntax.Bind(name, body) => {
        names.push(name)
        current = body
      }
      _ => fail("expected a binder")
    }
  }
  assert_eq(names[0].text(), "x")
  assert_eq(names[1].text(), "x_1")
  assert_eq(names[DEPTH - 1].text(), "x_" + (DEPTH - 1).to_string())
  // the body is `f` applied to the binders in order, one argument per node
  for i = DEPTH - 1; i >= 0; i = i - 1 {
    match current {
      @syntax.Apply(head, [@syntax.Variable(name)]) if name == names[i] =>
        current = head
      _ => fail("expected an application to the next binder")
    }
  }
  assert_true(current is @syntax.Variable(name) && name == f)
}

///|
test "deep terms: eta-long normal form of a long spine" {
  // `f c ... c` at `B` quotes back to `Apply(...Apply(f, [c])..., [c])`
  let a = base("A")
  let b = base("B")
  let f = @core.Name::new("f")
  let ctx = @stlc.TypeContext::empty().extend_with(f, deep_arrow(DEPTH, a, b))
  let term = spine(tm_var("f"), Array::make(DEPTH, con("c")))
  let mut current = match
    @stlc.normalize_eta_long(deep_signature(), ctx, term, b) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  for _ in 0..<DEPTH {
    match current {
      @syntax.Apply(head, [@syntax.Value(Const(name))]) if name.text() == "c" =>
        current = head
      _ => fail("expected an application to `c`")
    }
  }
  assert_true(current is @syntax.Variable(name) && name == f)
}

///|
test "deep terms: checked normalization under deep binders" {
  // `λx0. ... λx(DEPTH-1). (λy. y) x0` takes one beta step
  let a = base("A")
  let term = deep_lambda(DEPTH, app(lam("y", tm_var("y")), tm_var("x0")))
  match
    @stlc.normalize_checked(
      deep_signature(),
      @stlc.TypeContext::empty(),
      term,
      deep_arrow(DEPTH, a, a),
      10,
    ) {
    Ok(NormalForm(term=normal, steps=1)) => {
      let mut current = normal
      for _ in 0..<DEPTH {
        match current {
          @syntax.Bind(_, body) => current = body
          _ => fail("expected a binder")
        }
      }
      assert_true(current is @syntax.Variable(name) && name.text() == "x0")
    }
    _ => fail("expected a normal form after one step")
  }
}

///|
/// `(...((domain -> result) -> result) ...) -> result` with `arrows` arrows,
/// nested in the domains.
fn deep_domain(arrows : Int, domain : @stlc.Ty, result : @stlc.Ty) -> @stlc.Ty {
  let mut ty = domain
  for _ in 0..<arrows {
    ty = Arrow(ty, result)
  }
  ty
}

///|
test "deep types: types nested in their domains" {
  let a = base("A")
  let b = base("B")
  let ty = deep_domain(DEPTH, a, b)
  assert_true(ty == deep_domain(DEPTH, a, b))
  assert_true(ty != deep_domain(DEPTH, b, b))
  let g = @core.Name::new("g")
  let ctx = @stlc.TypeContext::empty().extend_with(g, ty)
  let sig = @stlc.Signature::empty()
  assert_true(
    @stlc.check(sig, ctx, tm_var("g"), deep_domain(DEPTH, a, b)) is Ok(_),
  )
  match @stlc.check(sig, ctx, tm_var("g"), deep_domain(DEPTH, b, b)) {
    Err(TypeMismatch(actual~, ..)) => assert_true(physical_equal(actual, ty))
    _ => fail("expected a type mismatch")
  }
  // `λx. g x` against the deep type: the parameter gets the deep domain
  assert_true(
    @stlc.check(sig, ctx, lam("x", app(tm_var("g"), tm_var("x"))), ty) is Ok(_),
  )
}

///|
test "deep types: eta-long normal form at a type nested in its domains" {
  // `g : ((A -> B) -> B) ... -> B` normalizes to
  // `λx. g (λx_1. x (λx_2. x_1 (... x_(DEPTH-1))))`, two nodes per level
  let a = base("A")
  let b = base("B")
  let ty = deep_domain(DEPTH, a, b)
  let g = @core.Name::new("g")
  let ctx = @stlc.TypeContext::empty().extend_with(g, ty)
  let mut current = match
    @stlc.normalize_eta_long(@stlc.Signature::empty(), ctx, tm_var("g"), ty) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  // level `i` is `λx_i. f a` where `f` is `g` at the top and the binder of
  // the level above otherwise, and `a` is the next level; the innermost
  // argument is the innermost binder `x_(DEPTH-1)`
  let mut function = g
  for level in 0..<DEPTH {
    let expected = if level == 0 { "x" } else { "x_" + level.to_string() }
    match current {
      @syntax.Bind(name, @syntax.Apply(@syntax.Variable(head), [argument])) if name.text() ==
        expected &&
        head == function => {
        current = argument
        function = name
      }
      _ => fail("expected the binder " + expected)
    }
  }
  assert_true(current is @syntax.Variable(name) && name == function)
}
