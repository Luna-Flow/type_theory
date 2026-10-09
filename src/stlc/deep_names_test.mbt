// Deep terms (issue #13) whose normalization also needs `@syntax.all_names`
// on the deep input term, which is stack-safe only with the `syntax` fix.

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
