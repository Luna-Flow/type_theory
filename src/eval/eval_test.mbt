///|
fn drop_zero(term : @syntax.Term[String]) -> @syntax.Term[String]? {
  match term {
    Apply(Value("+"), [Value("0"), other]) => Some(other)
    _ => None
  }
}

///|
test "applicative order keeps fixed-arity rules innermost" {
  // issue #11: a rule that matches whole applications of one arity never
  // matches a shorter prefix, so the inner redex is still contracted first
  let rule = @rewrite.RuleName::unsafe_new("drop_zero")
  let inner : @syntax.Term[String] = Apply(Value("+"), [Value("0"), Value("1")])
  let outer : @syntax.Term[String] = Apply(Value("+"), [Value("0"), inner])
  match @eval.reduce_once(outer, rule, drop_zero, ApplicativeOrder) {
    Reduced(after~, path~, ..) => {
      assert_true(after == Apply(Value("+"), [Value("0"), Value("1")]))
      assert_true(path.to_array() == [@rewrite.ApplyArgument(1)])
    }
    NoStep => assert_false(true)
  }
  assert_true(
    @eval.evaluate(outer, rule, drop_zero, ApplicativeOrder, 10) ==
    NormalForm(term=Value("1"), steps=2),
  )
}

///|
test "applicative order rewrites only addressable positions" {
  // issue #11: a prefix `Apply(f, [a])` of `Apply(f, [a, b])` only decides
  // when the whole application is tried; it is never rewritten on its own
  let unary_f = fn(term : @syntax.Term[String]) -> @syntax.Term[String]? {
    match term {
      Apply(Value("f"), [_]) => Some(Value("done"))
      _ => None
    }
  }
  let rule = @rewrite.RuleName::unsafe_new("unary_f")
  let term : @syntax.Term[String] = Apply(Value("f"), [Value("a"), Value("b")])
  assert_true(
    @eval.reduce_once(term, rule, unary_f, ApplicativeOrder) is NoStep,
  )
  assert_true(@eval.reduce_once(term, rule, unary_f, NormalOrder) is NoStep)
}

///|
test "applicative order tries an application once its first redex prefix is complete" {
  // issue #11: a rule that consumes the head and the first argument, keeping
  // the rest of the spine, is contracted before the later arguments
  let first = fn(term : @syntax.Term[String]) -> @syntax.Term[String]? {
    match term {
      Apply(Value("first"), [argument]) => Some(argument)
      Apply(Value("first"), [argument, .. rest]) =>
        Some(Apply(argument, rest.to_owned()))
      _ => None
    }
  }
  let rule = @rewrite.RuleName::unsafe_new("first")
  let inner : @syntax.Term[String] = Apply(Value("first"), [Value("b")])
  let term : @syntax.Term[String] = Apply(Value("first"), [Value("a"), inner])
  match @eval.reduce_once(term, rule, first, ApplicativeOrder) {
    Reduced(before~, after~, path~, ..) => {
      assert_true(before == term)
      assert_true(after == Apply(Value("a"), [inner]))
      assert_true(path.to_array() == [])
    }
    NoStep => assert_false(true)
  }
}
