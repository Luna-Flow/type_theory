# core tutorial

This tutorial shows how to create variable names, generate fresh ones, keep
track of the names in scope and rename variables with the `core` package. By
the end you can give your own syntax a name type that the rest of
`type_theory` understands.

| I want to | Use |
| --- | --- |
| make a variable name | `@core.Name::new("x")` |
| pick a name that clashes with nothing in use | `@core.fresh_name(hint, used)` |
| record the names in scope | `Context`, `extend_with` |
| record binders with annotations in order | `Telescope` |
| rename several variables at once | `Renaming`, `apply`, `then`, `without` |

## Quick start

Add the module and import the package:

```bash
moon add Luna-Flow/type_theory@0.3.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "moonbitlang/core/immut/hashset",
}
```

The smallest useful program picks a name that does not clash with the names
already in use:

```moonbit
test "quick start: a fresh name" {
  let used = @hashset.HashSet([@core.Name::new("x"), @core.Name::new("x_1")])
  let fresh = @core.fresh_name(@core.Name::new("x"), used)
  inspect(fresh.text(), content="x_2")
}
```

`fresh_name` keeps the hint `x` when it is unused and otherwise appends the
smallest suffix `_1`, `_2`, … that is not taken.

## Everyday tasks

### Name the parameters of a generated function

When a program generates code, it often needs several parameter names that
avoid each other and the names already in the surrounding code. Add each new
name to the used set before choosing the next:

```moonbit
test "choose several distinct parameter names" {
  let mut used = @hashset.HashSet([@core.Name::new("x")])
  let params : Array[String] = []
  for _ in 0..<3 {
    let p = @core.fresh_name(@core.Name::new("x"), used)
    used = used.add(p)
    params.push(p.text())
  }
  inspect(params.join(", "), content="x_1, x_2, x_3")
}
```

The result depends only on the hint and the used set, so the same input
always produces the same names.

### Track the names in scope

A `Context` records binders from the outside in. A later binder with the same
name shadows an earlier one, and the context keeps both:

```moonbit
test "track binders while walking into a term" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let outer = @core.Context::empty().extend_with(x)
  let inner = outer.extend_with(y).extend_with(x)
  assert_eq(outer.length(), 1)
  assert_eq(inner.length(), 3)
  assert_true(inner.contains(y))
  assert_false(outer.contains(y))
}
```

`extend_with` returns a new context and leaves `outer` unchanged, so you can
keep the context of each level of a traversal without copying it yourself.

### Rename variables

A `Renaming` maps some names to others and leaves every other name alone. All
entries apply at once:

```moonbit
test "swap two names simultaneously" {
  let a = @core.Name::new("a")
  let b = @core.Name::new("b")
  let swap = @core.Renaming::singleton(a, b).set(b, a)
  assert_eq(swap.apply(a), b)
  assert_eq(swap.apply(b), a)
  assert_eq(swap.apply(@core.Name::new("c")), @core.Name::new("c"))
}
```

Because the renaming is simultaneous, swapping needs no temporary name.

### Compose renamings and respect binders

`r.then(s)` applies `r` and then `s`. Under a binder for `x`, remove `x` from
the renaming with `without`, because the bound `x` is a different variable:

```moonbit
test "compose and shadow" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let r = @core.Renaming::singleton(x, y).then(@core.Renaming::singleton(y, z))
  assert_eq(r.apply(x), z)
  let under_x = r.without(x)
  assert_eq(under_x.apply(x), x)
  assert_eq(under_x.apply(y), z)
}
```

### Describe a parameter list with a telescope

A `Telescope` stores binders with annotations, in the order in which later
annotations may refer to earlier binders:

```moonbit
test "a dependent parameter list" {
  let n = @core.Name::new("n")
  let v = @core.Name::new("v")
  let params : @core.Telescope[String] = @core.Telescope::empty()
    .extend_with(n, "Nat")
    .extend_with(v, "Vec(n)")
  let shown = params.to_array().map(p => "\{p.0.text()} : \{p.1}")
  inspect(shown.join(", "), content="n : Nat, v : Vec(n)")
}
```

## Going further

### Bridge your own variable type

A downstream library usually has its own variable type, for example a
variable with an index. Give it a conversion to
`Name` so that it can use the binding algorithms of `type_theory`:

```moonbit
pub struct MyVar {
  index : Int
}

pub fn MyVar::to_name(self : MyVar) -> @core.Name {
  @core.Name::new("v" + self.index.to_string())
}

test "downstream variables become names" {
  let v : MyVar = { index: 3 }
  inspect(v.to_name().text(), content="v3")
}
```

The conversion must be injective on the variables you use: two different
variables must not map to the same name.

### Avoid all names, not only free ones

`fresh_name` only knows the set you give it. When you rename a binder, put
every name of the term into that set (free, bound and binder names), plus the
names of anything you are about to insert. The [syntax](../api/syntax.md)
helpers `all_names` and `generic_all_names` compute this set.

## Common pitfalls

- **Comparing renamings.** `==` on `Renaming` compares entry lists. Two
  renamings that act the same, such as `empty()` and `singleton(x, x)`, are
  not `==`. Compare their action on the names you care about instead.
- **Mutating a context.** There is nothing to mutate: `extend_with` returns a
  new value. Forgetting to use the result is the usual mistake.
- **Old method names.** `Context::extend`, `Telescope::extend` and the
  `extend` forms in `stlc` are deprecated aliases; use `extend_with`.
- **Long contexts.** Every `extend_with` copies the array. Building a context
  of $n$ names one by one costs $O(n^2)$; use `Context::from_array` when you
  have all names at once.

## Next steps

- The [core API](../api/core.md) lists every function with its exact
  signature.
- The [core design](../design/core.md) proves the freshness and composition
  laws used here.
- The [syntax tutorial](syntax.md) uses names to build terms with binders.
