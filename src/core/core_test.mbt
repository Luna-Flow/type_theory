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

///|
test "context to_array returns a copy" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let ctx = @core.Context::from_array([x])
  let names = ctx.to_array()
  names.push(x)
  names[0] = y
  assert_eq(ctx.length(), 1)
  assert_true(ctx.contains(x))
  assert_false(ctx.contains(y))
  assert_true(ctx.to_array() == [x])
  assert_true(ctx == @core.Context::from_array([x]))
}

///|
test "context from_array does not alias its argument" {
  let x = @core.Name::new("x")
  let names = [x]
  let ctx = @core.Context::from_array(names)
  names.push(@core.Name::new("y"))
  assert_eq(ctx.length(), 1)
}

///|
test "telescope to_array returns a copy" {
  let x = @core.Name::new("x")
  let telescope : @core.Telescope[Int] = @core.Telescope::empty().extend_with(
    x, 1,
  )
  let entries = telescope.to_array()
  entries.push((x, 2))
  entries[0] = (x, 3)
  assert_eq(telescope.length(), 1)
  assert_true(telescope.to_array() == [(x, 1)])
}

///|
test "renaming to_array returns a copy" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let renaming = @core.Renaming::singleton(x, y)
  let entries = renaming.to_array()
  entries.push((x, z))
  entries[0] = (x, z)
  assert_eq(renaming.length(), 1)
  assert_true(renaming.apply(x) == y)
  assert_true(renaming.to_array() == [(x, y)])
  assert_true(renaming == @core.Renaming::singleton(x, y))
}

///|
test "renaming length counts each source name once" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let renaming = @core.Renaming::empty().set(x, y).set(x, z).set(y, x)
  assert_eq(renaming.length(), 2)
  assert_true(renaming.to_array() == [(x, z), (y, x)])
  assert_eq(renaming.without(x).length(), 1)
}
