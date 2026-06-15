///|
test "fresh names preserve the hint and add stable suffixes" {
  let x = Name::new("x")
  let used = @hashset.from_array([x, Name::new("x_1")])
  assert_true(fresh_name(Name::new("y"), used) == Name::new("y"))
  assert_true(fresh_name(x, used) == Name::new("x_2"))
}

///|
test "renaming composition follows application order" {
  let x = Name::new("x")
  let y = Name::new("y")
  let z = Name::new("z")
  let composed = Renaming::singleton(x, y).then(Renaming::singleton(y, z))
  assert_true(composed.apply(x) == z)
  assert_true(composed.apply(y) == z)
}
