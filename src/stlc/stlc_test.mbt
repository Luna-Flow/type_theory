///|
fn base(name : String) -> Ty {
  Ty::Base(@core.Name::new(name))
}

///|
fn tm_var(name : String) -> Term {
  @syntax.Variable(@core.Name::new(name))
}

///|
fn con(name : String) -> Term {
  @syntax.Value(Atom::Const(@core.Name::new(name)))
}

///|
fn unit_term() -> Term {
  @syntax.Value(Atom::UnitLit)
}

///|
fn lam(name : String, body : Term) -> Term {
  @syntax.Bind(@core.Name::new(name), body)
}

///|
fn app(function : Term, argument : Term) -> Term {
  @syntax.Apply(function, [argument])
}

///|
test "typechecks identity" {
  let a = base("A")
  let term = lam("x", tm_var("x"))
  assert_true(
    check(Signature::empty(), TypeContext::empty(), term, Ty::Arrow(a, a)) ==
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
    check(
      Signature::empty(),
      TypeContext::empty(),
      const_term,
      Ty::Arrow(a, Ty::Arrow(b, a)),
    ) ==
    Ok(()),
  )
  assert_true(
    check(
      Signature::empty(),
      TypeContext::empty(),
      apply_term,
      Ty::Arrow(Ty::Arrow(a, b), Ty::Arrow(a, b)),
    ) ==
    Ok(()),
  )
}

///|
test "typechecks unit identity and constant application" {
  let c = @core.Name::new("c")
  let sig = Signature::empty().extend(c, Ty::Arrow(Ty::Unit, Ty::Unit))
  let unit_id = lam("x", tm_var("x"))
  assert_true(
    check(
      Signature::empty(),
      TypeContext::empty(),
      unit_id,
      Ty::Arrow(Ty::Unit, Ty::Unit),
    ) ==
    Ok(()),
  )
  assert_true(
    infer(sig, TypeContext::empty(), app(con("c"), unit_term())) == Ok(Ty::Unit),
  )
}

///|
test "rejects unbound variable and unknown constant" {
  assert_true(
    infer(Signature::empty(), TypeContext::empty(), tm_var("x")) ==
    Err(TypeError::UnboundVariable(@core.Name::new("x"))),
  )
  assert_true(
    infer(Signature::empty(), TypeContext::empty(), con("c")) ==
    Err(TypeError::UnknownConstant(@core.Name::new("c"))),
  )
}

///|
test "rejects lambda inference and non-function application" {
  let a = base("A")
  assert_true(
    infer(Signature::empty(), TypeContext::empty(), lam("x", tm_var("x"))) ==
    Err(TypeError::CannotInferLambda),
  )
  assert_true(
    infer(
      Signature::empty(),
      TypeContext::empty().extend(@core.Name::new("x"), a),
      app(tm_var("x"), unit_term()),
    ) ==
    Err(TypeError::ExpectedFunction(a)),
  )
}

///|
test "rejects argument mismatch and empty application" {
  let a = base("A")
  let b = base("B")
  let sig = Signature::empty().extend(@core.Name::new("f"), Ty::Arrow(a, a))
  assert_true(
    infer(
      sig,
      TypeContext::empty().extend(@core.Name::new("u"), b),
      app(con("f"), tm_var("u")),
    ) ==
    Err(TypeError::TypeMismatch(expected=a, actual=b)),
  )
  assert_true(
    infer(
      Signature::empty(),
      TypeContext::empty(),
      @syntax.Apply(tm_var("x"), []),
    ) ==
    Err(TypeError::EmptyApplication),
  )
}

///|
test "shadowing uses nearest binder" {
  let a = base("A")
  let b = base("B")
  let term = lam("x", lam("x", tm_var("x")))
  assert_true(
    check(
      Signature::empty(),
      TypeContext::empty(),
      term,
      Ty::Arrow(a, Ty::Arrow(b, b)),
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
    normalize_checked(
      Signature::empty(),
      TypeContext::empty(),
      id_unit,
      Ty::Unit,
      10,
    ) ==
    Ok(@rewrite.NormalForm(term=unit_term(), steps=1)),
  )
  assert_true(
    normalize_checked(
      Signature::empty(),
      TypeContext::empty(),
      const_unit,
      Ty::Unit,
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
    normalize_checked(
      Signature::empty(),
      TypeContext::empty().extend(@core.Name::new("x"), a),
      bad,
      Ty::Unit,
      10,
    ) ==
    Err(TypeError::ExpectedFunction(a)),
  )
}

///|
test "typed eta long nbe eta expands open functions" {
  let a = base("A")
  let b = base("B")
  let f = @core.Name::new("f")
  let expected = lam("x", app(tm_var("f"), tm_var("x")))
  match
    normalize_eta_long(
      Signature::empty(),
      TypeContext::empty().extend(f, Ty::Arrow(a, b)),
      tm_var("f"),
      Ty::Arrow(a, b),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
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
    normalize_eta_long(
      Signature::empty(),
      TypeContext::empty(),
      id_term,
      Ty::Arrow(a, a),
    ) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, id_term))
    Err(_) => assert_false(true)
  }
  match
    normalize_eta_long(
      Signature::empty(),
      TypeContext::empty().extend(g, Ty::Arrow(a, a)).extend(y, a),
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
  let ctx = TypeContext::empty().extend(@core.Name::new("y"), a)
  match normalize_eta_long(Signature::empty(), ctx, term, a) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, tm_var("y")))
    Err(_) => assert_false(true)
  }
}
