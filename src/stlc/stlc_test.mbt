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
