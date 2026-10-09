///|
test "issue 27: nested redex arguments normalize without repeated inference" {
  let a = base("A")
  let identity = lam("x", tm_var("x"))
  let mut term = con("c")
  for _ in 0..<100_000 {
    term = app(identity, term)
  }
  let sig = @stlc.Signature::empty().extend_with(@core.Name::new("c"), a)
  match @stlc.normalize_eta_long(sig, @stlc.TypeContext::empty(), term, a) {
    Ok(@syntax.Value(@stlc.Atom::Const(name))) if name.text() == "c" => ()
    _ => fail("expected normalization to the constant")
  }
}

///|
test "issue 27: deep neutral argument positions" {
  let a = base("A")
  let sig = deep_signature()
  let mut term = con("c")
  for _ in 0..<100_000 {
    term = app(con("d"), term)
  }
  let mut normal = match
    @stlc.normalize_eta_long(sig, @stlc.TypeContext::empty(), term, a) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  for _ in 0..<100_000 {
    match normal {
      @syntax.Apply(@syntax.Value(Const(name)), [argument]) if name.text() ==
        "d" => normal = argument
      _ => fail("expected a neutral d application")
    }
  }
  assert_true(normal is @syntax.Value(Const(name)) && name.text() == "c")
}

///|
test "issue 27: first errors match checking before evaluation" {
  let a = base("A")
  let ctx = @stlc.TypeContext::empty()
  let sig = deep_signature()
  let cases = [
    (app(lam("x", con("body_missing")), con("arg_missing")), a),
    (app(lam("x", @syntax.Apply(tm_var("x"), [])), con("arg_missing")), a),
    (app(lam("x", @syntax.Apply(tm_var("x"), [])), con("c")), a),
    (spine(con("d"), [unit_term(), con("arg_missing")]), a),
    (spine(lam("x", tm_var("x")), [con("c"), con("arg_missing")]), a),
    (app(lam("x", lam("y", tm_var("y"))), unit_term()), a),
    (app(lam("x", tm_var("x")), lam("y", tm_var("y"))), Arrow(a, a)),
  ]
  for (term, ty) in cases {
    match @stlc.check(sig, ctx, term, ty) {
      Err(expected) =>
        match @stlc.normalize_eta_long(sig, ctx, term, ty) {
          Err(actual) => assert_true(actual == expected)
          Ok(_) => fail("normalization accepted rejected input")
        }
      Ok(_) => fail("expected rejected input")
    }
  }
}

///|
test "issue 27: renamed redexes preserve free names and binder choices" {
  let a = base("A")
  let ctx = @stlc.TypeContext::empty().extend_with(@core.Name::new("x"), a)
  let term = spine(lam("x", lam("y", lam("z", tm_var("y")))), [
    unit_term(),
    tm_var("x"),
  ])
  let ty = @stlc.Ty::Arrow(a, a)
  match @stlc.normalize_eta_long(@stlc.Signature::empty(), ctx, term, ty) {
    Ok(normal) => assert_true(normal == lam("x_1", tm_var("x")))
    Err(_) => fail("normalization failed")
  }
}
