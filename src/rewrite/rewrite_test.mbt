///|
test "rule names report validation failures as data" {
  assert_true(RuleName::new("") == Err(RuleNameError::Empty))
  match RuleName::new("beta") {
    Ok(name) => assert_true(name.value() == "beta")
    Err(_) => assert_false(true)
  }
}

///|
test "structured step records rule and root path" {
  let decrement = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Value(value) if value > 0 => Some(Value(value - 1))
      _ => None
    }
  }
  let rule = RuleName::unsafe_new("decrement")
  match top_down_once(@syntax.Value(2), rule, decrement) {
    Reduced(before~, after~, rule=used_rule, path~) => {
      assert_true(before == @syntax.Value(2))
      assert_true(after == @syntax.Value(1))
      assert_true(used_rule == rule)
      assert_true(path.to_array().length() == 0)
    }
    NoStep => assert_false(true)
  }
}

///|
test "normalizer and trace are built from single steps" {
  let decrement = fn(term : @syntax.Term[Int]) -> @syntax.Term[Int]? {
    match term {
      Value(value) if value > 0 => Some(Value(value - 1))
      _ => None
    }
  }
  let rule = RuleName::unsafe_new("decrement")
  let step = fn(term) { top_down_once(term, rule, decrement) }
  assert_true(
    normalize(@syntax.Value(2), step, 2) ==
    NormalForm(term=@syntax.Value(0), steps=2),
  )
  let reduction_trace = trace(@syntax.Value(2), step, 1)
  assert_true(reduction_trace.steps().length() == 1)
  assert_true(
    reduction_trace.result() == StepLimitReached(term=@syntax.Value(1), steps=1),
  )
}
