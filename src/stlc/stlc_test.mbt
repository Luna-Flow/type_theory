///|
fn base(name : String) -> @stlc.Ty {
  @stlc.Ty::Base(@core.Name::new(name))
}

///|
fn tm_var(name : String) -> @stlc.Term {
  @syntax.Variable(@core.Name::new(name))
}

///|
fn con(name : String) -> @stlc.Term {
  @syntax.Value(@stlc.Atom::Const(@core.Name::new(name)))
}

///|
fn unit_term() -> @stlc.Term {
  @syntax.Value(@stlc.Atom::UnitLit)
}

///|
fn lam(name : String, body : @stlc.Term) -> @stlc.Term {
  @syntax.Bind(@core.Name::new(name), body)
}

///|
fn app(function : @stlc.Term, argument : @stlc.Term) -> @stlc.Term {
  @syntax.Apply(function, [argument])
}

///|
test "typechecks identity" {
  let a = base("A")
  let term = lam("x", tm_var("x"))
  assert_true(
    @stlc.check(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      term,
      @stlc.Ty::Arrow(a, a),
    ) ==
    Ok(()),
  )
}

///|
test "typechecks const and apply combinators" {
  let a = base("A")
  let b = base("B")
  let const_term = lam("x", lam("y", tm_var("x")))
  let apply_term = lam("f", lam("x", app(tm_var("f"), tm_var("x"))))
  assert_true(
    @stlc.check(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      const_term,
      @stlc.Ty::Arrow(a, @stlc.Ty::Arrow(b, a)),
    ) ==
    Ok(()),
  )
  assert_true(
    @stlc.check(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      apply_term,
      @stlc.Ty::Arrow(@stlc.Ty::Arrow(a, b), @stlc.Ty::Arrow(a, b)),
    ) ==
    Ok(()),
  )
}

///|
test "typechecks unit identity and constant application" {
  let c = @core.Name::new("c")
  let sig = @stlc.Signature::empty().extend_with(
    c,
    @stlc.Ty::Arrow(@stlc.Ty::Unit, @stlc.Ty::Unit),
  )
  let unit_id = lam("x", tm_var("x"))
  assert_true(
    @stlc.check(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      unit_id,
      @stlc.Ty::Arrow(@stlc.Ty::Unit, @stlc.Ty::Unit),
    ) ==
    Ok(()),
  )
  assert_true(
    @stlc.infer(sig, @stlc.TypeContext::empty(), app(con("c"), unit_term())) ==
    Ok(@stlc.Ty::Unit),
  )
}

///|
test "rejects unbound variable and unknown constant" {
  assert_true(
    @stlc.infer(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      tm_var("x"),
    ) ==
    Err(@stlc.TypeError::UnboundVariable(@core.Name::new("x"))),
  )
  assert_true(
    @stlc.infer(@stlc.Signature::empty(), @stlc.TypeContext::empty(), con("c")) ==
    Err(@stlc.TypeError::UnknownConstant(@core.Name::new("c"))),
  )
}

///|
test "rejects lambda inference and non-function application" {
  let a = base("A")
  assert_true(
    @stlc.infer(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      lam("x", tm_var("x")),
    ) ==
    Err(@stlc.TypeError::CannotInferLambda),
  )
  assert_true(
    @stlc.infer(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), a),
      app(tm_var("x"), unit_term()),
    ) ==
    Err(@stlc.TypeError::ExpectedFunction(a)),
  )
}

///|
test "rejects argument mismatch and empty application" {
  let a = base("A")
  let b = base("B")
  let sig = @stlc.Signature::empty().extend_with(
    @core.Name::new("f"),
    @stlc.Ty::Arrow(a, a),
  )
  assert_true(
    @stlc.infer(
      sig,
      @stlc.TypeContext::empty().extend_with(@core.Name::new("u"), b),
      app(con("f"), tm_var("u")),
    ) ==
    Err(@stlc.TypeError::TypeMismatch(expected=a, actual=b)),
  )
  assert_true(
    @stlc.infer(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      @syntax.Apply(tm_var("x"), []),
    ) ==
    Err(@stlc.TypeError::EmptyApplication),
  )
}

///|
test "shadowing uses nearest binder" {
  let a = base("A")
  let b = base("B")
  let term = lam("x", lam("x", tm_var("x")))
  assert_true(
    @stlc.check(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      term,
      @stlc.Ty::Arrow(a, @stlc.Ty::Arrow(b, b)),
    ) ==
    Ok(()),
  )
}

///|
test "checked operational normalization uses lambda reducer" {
  let id_unit = app(lam("x", tm_var("x")), unit_term())
  let const_unit = app(
    app(lam("x", lam("y", tm_var("x"))), unit_term()),
    unit_term(),
  )
  assert_true(
    @stlc.normalize_checked(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      id_unit,
      @stlc.Ty::Unit,
      10,
    ) ==
    Ok(@rewrite.NormalForm(term=unit_term(), steps=1)),
  )
  assert_true(
    @stlc.normalize_checked(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      const_unit,
      @stlc.Ty::Unit,
      10,
    ) ==
    Ok(@rewrite.NormalForm(term=unit_term(), steps=2)),
  )
}

///|
test "checked operational normalization rejects ill-typed terms first" {
  let a = base("A")
  let bad = app(tm_var("x"), unit_term())
  assert_true(
    @stlc.normalize_checked(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), a),
      bad,
      @stlc.Ty::Unit,
      10,
    ) ==
    Err(@stlc.TypeError::ExpectedFunction(a)),
  )
}

///|
test "typed eta long nbe eta expands open functions" {
  let a = base("A")
  let b = base("B")
  let f = @core.Name::new("f")
  let expected = lam("x", app(tm_var("f"), tm_var("x")))
  match
    @stlc.normalize_eta_long(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty().extend_with(f, @stlc.Ty::Arrow(a, b)),
      tm_var("f"),
      @stlc.Ty::Arrow(a, b),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe eta expands functional constants" {
  let a = base("A")
  let b = base("B")
  let c = @core.Name::new("c")
  let sig = @stlc.Signature::empty().extend_with(c, @stlc.Ty::Arrow(a, b))
  let expected = lam("x", app(con("c"), tm_var("x")))
  match
    @stlc.normalize_eta_long(
      sig,
      @stlc.TypeContext::empty(),
      con("c"),
      @stlc.Ty::Arrow(a, b),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe eta expands nested functional constants" {
  let a = base("A")
  let b = base("B")
  let c_ty = base("C")
  let c = @core.Name::new("c")
  let sig = @stlc.Signature::empty().extend_with(
    c,
    @stlc.Ty::Arrow(a, @stlc.Ty::Arrow(b, c_ty)),
  )
  let expected = lam(
    "x",
    lam("y", app(app(con("c"), tm_var("x")), tm_var("y"))),
  )
  match
    @stlc.normalize_eta_long(
      sig,
      @stlc.TypeContext::empty(),
      con("c"),
      @stlc.Ty::Arrow(a, @stlc.Ty::Arrow(b, c_ty)),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe quotes higher order neutral lambda arguments" {
  let a = base("A")
  let b = base("B")
  let h = @core.Name::new("h")
  let sig = @stlc.Signature::empty().extend_with(
    h,
    @stlc.Ty::Arrow(@stlc.Ty::Arrow(a, a), b),
  )
  let argument = lam("x", tm_var("x"))
  let term = app(con("h"), argument)
  match @stlc.normalize_eta_long(sig, @stlc.TypeContext::empty(), term, b) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, term))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe quotes higher order neutral open function arguments" {
  let a = base("A")
  let b = base("B")
  let h = @core.Name::new("h")
  let f = @core.Name::new("f")
  let sig = @stlc.Signature::empty().extend_with(
    h,
    @stlc.Ty::Arrow(@stlc.Ty::Arrow(a, a), b),
  )
  let ctx = @stlc.TypeContext::empty().extend_with(f, @stlc.Ty::Arrow(a, a))
  let term = app(con("h"), tm_var("f"))
  let expected = app(con("h"), lam("x", app(tm_var("f"), tm_var("x"))))
  match @stlc.normalize_eta_long(sig, ctx, term, b) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe applies function constants to unit" {
  let c = @core.Name::new("c")
  let sig = @stlc.Signature::empty().extend_with(
    c,
    @stlc.Ty::Arrow(@stlc.Ty::Unit, @stlc.Ty::Unit),
  )
  let term = app(con("c"), unit_term())
  match
    @stlc.normalize_eta_long(
      sig,
      @stlc.TypeContext::empty(),
      term,
      @stlc.Ty::Unit,
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, term))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe preserves identity and open neutral heads" {
  let a = base("A")
  let id_term = lam("x", tm_var("x"))
  let g = @core.Name::new("g")
  let y = @core.Name::new("y")
  match
    @stlc.normalize_eta_long(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty(),
      id_term,
      @stlc.Ty::Arrow(a, a),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, id_term))
    Err(_) => assert_false(true)
  }
  match
    @stlc.normalize_eta_long(
      @stlc.Signature::empty(),
      @stlc.TypeContext::empty()
      .extend_with(g, @stlc.Ty::Arrow(a, a))
      .extend_with(y, a),
      app(tm_var("g"), tm_var("y")),
      a,
    ) {
    Ok(normal) =>
      assert_true(@syntax.alpha_equal(normal, app(tm_var("g"), tm_var("y"))))
    Err(_) => assert_false(true)
  }
}

///|
test "typed eta long nbe agrees with beta and eta expectations" {
  let a = base("A")
  let term = app(lam("x", tm_var("x")), tm_var("y"))
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("y"), a)
  match @stlc.normalize_eta_long(@stlc.Signature::empty(), ctx, term, a) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, tm_var("y")))
    Err(_) => assert_false(true)
  }
}

///|
fn spine(head : @stlc.Term, arguments : Array[@stlc.Term]) -> @stlc.Term {
  @syntax.Apply(head, arguments)
}

///|
test "redex inference types trailing arguments in the outer context" {
  // Γ = x : B ⊢ (λx. λy. y) () x : B   (issue #1)
  let b = base("B")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), b)
  let term = spine(lam("x", lam("y", tm_var("y"))), [unit_term(), tm_var("x")])
  assert_true(@stlc.infer(sig, ctx, term) == Ok(b))
  assert_true(@stlc.check(sig, ctx, term, b) == Ok(()))
  assert_true(
    @stlc.check(sig, ctx, term, @stlc.Ty::Unit) ==
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
  assert_true(
    @stlc.normalize_checked(sig, ctx, term, @stlc.Ty::Unit, 10) ==
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
  assert_true(
    @stlc.normalize_checked(sig, ctx, term, b, 10) ==
    Ok(@rewrite.NormalForm(term=tm_var("x"), steps=2)),
  )
  match @stlc.normalize_eta_long(sig, ctx, term, b) {
    Ok(normal) => assert_true(normal == tm_var("x"))
    Err(_) => fail("well typed at B")
  }
}

///|
test "redex inference renames a parameter that is free in several trailing arguments" {
  // Γ = x : B, f : B -> A -> B ⊢ (λx. λg. λz. g z x) c f x : B   with c : A
  let a = base("A")
  let b = base("B")
  let sig = @stlc.Signature::empty().extend_with(@core.Name::new("c"), a)
  let ctx = @stlc.TypeContext::empty()
    .extend_with(@core.Name::new("x"), b)
    .extend_with(
      @core.Name::new("f"),
      @stlc.Ty::Arrow(b, @stlc.Ty::Arrow(a, b)),
    )
  // the parameter x : A is used in the body; the trailing x is the outer x : B
  let body = lam("g", lam("z", spine(tm_var("g"), [tm_var("z"), tm_var("x")])))
  let term = spine(lam("x", body), [con("c"), tm_var("f"), tm_var("x")])
  assert_true(@stlc.infer(sig, ctx, term) == Ok(b))
  let bad = spine(lam("x", lam("y", lam("w", tm_var("w")))), [
    con("c"),
    tm_var("x"),
    tm_var("x"),
  ])
  assert_true(@stlc.infer(sig, ctx, bad) == Ok(b))
  match @stlc.normalize_eta_long(sig, ctx, bad, b) {
    Ok(normal) => assert_true(normal == tm_var("x"))
    Err(_) => fail("well typed at B")
  }
}

///|
test "redex inference keeps the parameter when trailing arguments do not mention it" {
  // the parameter still shadows the outer x inside the body
  let a = base("A")
  let b = base("B")
  let sig = @stlc.Signature::empty().extend_with(@core.Name::new("c"), a)
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), b)
  let term = spine(lam("x", lam("y", tm_var("x"))), [con("c"), unit_term()])
  assert_true(@stlc.infer(sig, ctx, term) == Ok(a))
  let nested = spine(
    lam("x", spine(lam("x", lam("y", tm_var("y"))), [tm_var("x")])),
    [unit_term(), tm_var("x")],
  )
  assert_true(@stlc.infer(sig, ctx, nested) == Ok(b))
}

///|
test "empty applications are rejected anywhere in a spine" {
  // issue #2: STLC keeps rejecting empty applications, also nested ones
  let a = base("A")
  let ctx = @stlc.TypeContext::empty()
    .extend_with(@core.Name::new("f"), @stlc.Ty::Arrow(a, a))
    .extend_with(@core.Name::new("u"), a)
  let sig = @stlc.Signature::empty()
  let nested = @syntax.Term::Apply(@syntax.Term::Apply(tm_var("f"), []), [
    tm_var("u"),
  ])
  assert_true(
    @stlc.infer(sig, ctx, nested) == Err(@stlc.TypeError::EmptyApplication),
  )
  assert_true(
    @stlc.normalize_eta_long(sig, ctx, nested, a) ==
    Err(@stlc.TypeError::EmptyApplication),
  )
  let redex = @syntax.Term::Apply(
    @syntax.Term::Apply(lam("x", tm_var("x")), []),
    [tm_var("u")],
  )
  assert_true(
    @stlc.check(sig, ctx, redex, a) == Err(@stlc.TypeError::EmptyApplication),
  )
}

///|
/// Asserts that `check` accepts `term` at `ty`, and that `normalize_eta_long`
/// accepts it as well and returns `expected` up to alpha-equivalence.
fn assert_nbe_agrees_with_check(
  sig : @stlc.Signature,
  ctx : @stlc.TypeContext,
  term : @stlc.Term,
  ty : @stlc.Ty,
  expected : @stlc.Term,
) -> Unit raise {
  assert_true(@stlc.check(sig, ctx, term, ty) == Ok(()))
  match @stlc.normalize_eta_long(sig, ctx, term, ty) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => fail("check accepts the term, NbE rejects it")
  }
}

///|
test "typed eta long nbe accepts a curried redex head" {
  // Γ = x : B ⊢ ((λx. λy. y) ()) x : B   (issue #7, first shape)
  let b = base("B")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), b)
  let k = lam("x", lam("y", tm_var("y")))
  let term = app(app(k, unit_term()), tm_var("x"))
  assert_true(@stlc.infer(sig, ctx, term) == Ok(b))
  assert_nbe_agrees_with_check(sig, ctx, term, b, tm_var("x"))
  // the curried form of the issue #1 term must not capture the trailing x
  assert_true(
    @stlc.check(sig, ctx, term, @stlc.Ty::Unit) ==
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
  assert_true(
    @stlc.normalize_eta_long(sig, ctx, term, @stlc.Ty::Unit) ==
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
}

///|
test "typed eta long nbe accepts a redex body that consumes outer arguments" {
  // Γ = v : A ⊢ (λx. (λy. λz. z) x) () v : A   (issue #7, second shape)
  let a = base("A")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("v"), a)
  let inner = spine(lam("y", lam("z", tm_var("z"))), [tm_var("x")])
  let term = spine(lam("x", inner), [unit_term(), tm_var("v")])
  assert_true(@stlc.infer(sig, ctx, term) == Ok(a))
  assert_nbe_agrees_with_check(sig, ctx, term, a, tm_var("v"))
  // the same term with a curried spine
  let curried = app(
    app(
      lam("x", app(lam("y", lam("z", tm_var("z"))), tm_var("x"))),
      unit_term(),
    ),
    tm_var("v"),
  )
  assert_nbe_agrees_with_check(sig, ctx, curried, a, tm_var("v"))
}

///|
test "typed eta long nbe accepts deeply curried redex heads" {
  // Γ = u : A, v : B ⊢ (((λx. λy. λz. z) ()) u) v : B
  let a = base("A")
  let b = base("B")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty()
    .extend_with(@core.Name::new("u"), a)
    .extend_with(@core.Name::new("v"), b)
  let k3 = lam("x", lam("y", lam("z", tm_var("z"))))
  let three = app(app(app(k3, unit_term()), tm_var("u")), tm_var("v"))
  assert_nbe_agrees_with_check(sig, ctx, three, b, tm_var("v"))
  // ((λx. λy. y) ()) f at A -> B returns a neutral function: eta-expanded
  let f = @core.Name::new("f")
  let fctx = ctx.extend_with(f, @stlc.Ty::Arrow(a, b))
  let two = app(app(lam("x", lam("y", tm_var("y"))), unit_term()), tm_var("f"))
  assert_nbe_agrees_with_check(
    sig,
    fctx,
    two,
    @stlc.Ty::Arrow(a, b),
    lam("w", app(tm_var("f"), tm_var("w"))),
  )
  // a curried redex head selecting a neutral function, applied once more
  let pick = app(
    app(app(lam("g", lam("y", tm_var("g"))), tm_var("f")), unit_term()),
    tm_var("u"),
  )
  assert_nbe_agrees_with_check(
    sig,
    fctx,
    pick,
    b,
    app(tm_var("f"), tm_var("u")),
  )
}

///|
test "typed eta long nbe accepts mixed flat and nested spines" {
  // Γ = u : A, v : B ⊢ spines mixing Apply(h, [a1, a2]) and Apply(Apply(h, [a1]), [a2])
  let a = base("A")
  let b = base("B")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty()
    .extend_with(@core.Name::new("u"), a)
    .extend_with(@core.Name::new("v"), b)
  let k3 = lam("x", lam("y", lam("z", tm_var("z"))))
  let flat_then_nested = spine(spine(k3, [unit_term(), tm_var("u")]), [
    tm_var("v"),
  ])
  assert_nbe_agrees_with_check(sig, ctx, flat_then_nested, b, tm_var("v"))
  let nested_then_flat = spine(app(k3, unit_term()), [tm_var("u"), tm_var("v")])
  assert_nbe_agrees_with_check(sig, ctx, nested_then_flat, b, tm_var("v"))
  // redex body that is itself a curried redex consuming two outer arguments:
  // (λx. ((λp. λq. λr. q) x) u) () v w   with w : A
  let wctx = ctx.extend_with(@core.Name::new("w"), a)
  let body = app(
    app(lam("p", lam("q", lam("r", lam("s", tm_var("q"))))), tm_var("x")),
    tm_var("u"),
  )
  let term = spine(lam("x", body), [unit_term(), tm_var("v"), tm_var("w")])
  assert_true(@stlc.infer(sig, wctx, term) == Ok(a))
  assert_nbe_agrees_with_check(sig, wctx, term, a, tm_var("u"))
}

///|
test "typed eta long nbe renames a curried redex parameter apart from outer arguments" {
  // Γ = x : B ⊢ (λx. (λy. λz. z) x) () x : B — the trailing x is the outer x
  let b = base("B")
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), b)
  let inner = app(lam("y", lam("z", tm_var("z"))), tm_var("x"))
  let term = app(app(lam("x", inner), unit_term()), tm_var("x"))
  assert_true(@stlc.infer(sig, ctx, term) == Ok(b))
  assert_nbe_agrees_with_check(sig, ctx, term, b, tm_var("x"))
  assert_true(
    @stlc.normalize_eta_long(sig, ctx, term, @stlc.Ty::Unit) ==
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
  // the inner parameter y is also renamed apart from the outer x
  let inner_y = app(lam("x", lam("z", tm_var("z"))), tm_var("x"))
  let term_y = app(app(lam("x", inner_y), unit_term()), tm_var("x"))
  assert_nbe_agrees_with_check(sig, ctx, term_y, b, tm_var("x"))
}
