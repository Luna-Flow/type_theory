// Deep terms (issue #13) whose normalization also needs `@syntax.all_names`
// on the deep input term, made stack-safe by the `syntax` fix in #26.

///|
test "deep terms: eta-long normal form of a deep lambda" {
  // needs `@syntax.all_names` on the deep term
  let a = base("A")
  let ty = deep_arrow(DEPTH, a, a)
  let normal = match
    @stlc.normalize_eta_long(
      deep_signature(),
      @stlc.TypeContext::empty(),
      deep_lambda(DEPTH, tm_var("x0")),
      ty,
    ) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  let mut current = normal
  let mut first = None
  for _ in 0..<DEPTH {
    match current {
      @syntax.Bind(name, body) => {
        if first is None {
          first = Some(name)
        }
        current = body
      }
      _ => fail("expected a binder")
    }
  }
  assert_true(current is @syntax.Variable(name) && first == Some(name))
}

///|
test "readback fresh-name cursor agrees with core fresh_name" {
  let hint = @core.Name::new("x")
  let x = @core.Name::new("x")
  let x1 = @core.Name::new("x_1")
  let x3 = @core.Name::new("x_3")
  let f = @core.Name::new("f")
  let a = base("A")
  let ty = deep_arrow(8, a, a)
  let ctx = @stlc.TypeContext::empty()
    .extend_with(x, a)
    .extend_with(x1, a)
    .extend_with(x3, a)
    .extend_with(f, ty)
  let mut used = @hashset.HashSet([x, x1, x3, f])
  let expected : Array[@core.Name] = []
  for _ in 0..<8 {
    let next = @core.fresh_name(hint, used)
    expected.push(next)
    used = used.add(next)
  }
  let mut normal = match
    @stlc.normalize_eta_long(@stlc.Signature::empty(), ctx, tm_var("f"), ty) {
    Ok(normal) => normal
    Err(_) => fail("normalization failed")
  }
  for i in 0..<expected.length() {
    match normal {
      @syntax.Bind(name, body) => {
        assert_true(name == expected[i])
        normal = body
      }
      _ => fail("expected eta-expanded binder")
    }
  }
}
