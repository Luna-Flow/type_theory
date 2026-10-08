///|
test "fresh names preserve the hint and add stable suffixes" {
  let x = @core.Name::new("x")
  let used = @hashset.HashSet([x, @core.Name::new("x_1")])
  assert_true(
    @core.fresh_name(@core.Name::new("y"), used) == @core.Name::new("y"),
  )
  assert_true(@core.fresh_name(x, used) == @core.Name::new("x_2"))
}

///|
test "renaming composition follows application order" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let composed = @core.Renaming::singleton(x, y).then(
    @core.Renaming::singleton(y, z),
  )
  assert_true(composed.apply(x) == z)
  assert_true(composed.apply(y) == z)
}
