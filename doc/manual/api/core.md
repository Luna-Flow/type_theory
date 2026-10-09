# core API

## Purpose

The `core` package defines the vocabulary that every other package of
`type_theory` shares: variable names, fresh-name generation, ordered scopes,
telescopes and finite renamings. All values are immutable: every operation
that "changes" a value returns a new one and leaves its argument untouched.
`Context`, `Telescope` and `Renaming` are abstract types, so their storage
cannot be reached from outside the package, and every method that returns an
array returns a fresh copy.
None of these values is nested, so every operation, the derived `==`,
`compare`, `hash` and `Debug` included, uses a constant amount of host stack.
The mathematics behind these definitions is in the [core design](../design/core.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "moonbitlang/core/immut/hashset",
}
```

`hashset` is needed for the name sets that `fresh_name`, `Renaming::support`
and `Renaming::targets` take or return. The examples on this page refer to
every name through its package alias, for example `@core.Name`.

## Names

### `Name`

`Name` is a variable name, compared by its text.

```mbti
pub struct Name {
  text : String
} derive(Compare, Eq, Hash, @debug.Debug)
```

Two names are the same variable exactly when their texts are equal. A name
carries no scope, no unique identifier and no type: binding is decided by the
syntax that contains the name. The field `text` is read-only outside the
package; use `Name::new` and `Name::text`.

### `Name::new`

`Name::new` makes a name from its text.

```mbti
pub fn Name::new(String) -> Self
```

Any string is accepted, including the empty string and strings that look like
generated names such as `x_1`. The library never parses the text, except that
`fresh_name` appends `_<k>` suffixes to it.

### `Name::text`

`Name::text` returns the text of a name.

```mbti
pub fn Name::text(Self) -> String
```

```moonbit
test "name text round trip" {
  let x = @core.Name::new("x")
  inspect(x.text(), content="x")
  assert_true(x == @core.Name::new("x"))
  assert_true(x != @core.Name::new("y"))
}
```

### `Name::equal`, `Name::compare`, `Name::hash`

These methods compare and hash names through their text.

```mbti
pub fn Name::equal(Self, Self) -> Bool
pub fn Name::compare(Self, Self) -> Int
pub fn Name::hash(Self) -> Int
```

They are the `Eq`, `Compare` and `Hash` implementations promoted to methods.
`compare` is the order of `String` on the texts: shorter texts first, then
by UTF-16 code units. It is a total order, so names can be sorted for
deterministic output; `hash` lets names live in `HashSet` and `HashMap`.
Prefer the operators `==`, `!=`, `<` and friends in new code.

```moonbit
test "names are ordered by text" {
  let a = @core.Name::new("a")
  let b = @core.Name::new("b")
  assert_true(a < b)
  assert_eq(a.compare(b), -1)
  assert_true(@core.Name::new("z") < @core.Name::new("aa"))
}
```

### `fresh_name`

`fresh_name` returns a name that does not occur in a set of used names,
keeping a hint when possible.

```mbti
pub fn fresh_name(Name, @hashset.HashSet[Name]) -> Name
```

`fresh_name(hint, used)` returns `hint` itself when `hint` is not in `used`.
Otherwise it tries `hint_1`, `hint_2`, … in order and returns the first
candidate that is not in `used`. The result is a function of `hint` and
`used` only, so repeated runs produce the same names. It always terminates:
at most $|used| + 1$ candidates are tried.

```moonbit
test "fresh_name keeps the hint or adds a suffix" {
  let x = @core.Name::new("x")
  let used = @hashset.HashSet([x, @core.Name::new("x_1")])
  inspect(@core.fresh_name(@core.Name::new("y"), used).text(), content="y")
  inspect(@core.fresh_name(x, used).text(), content="x_2")
}
```

## Scopes

### `Context`

`Context` is an ordered list of names in scope, innermost last.

```mbti
type Context derive(Eq, @debug.Debug)
```

A context may contain the same name more than once; a later entry shadows an
earlier one. Two contexts are equal when they list the same names in the same
order. The type is abstract: read a context with `length`, `contains` and
`to_array`.

### `Context::empty`, `Context::from_array`

These functions build a context with no names, or with the names of an array
in order.

```mbti
pub fn Context::empty() -> Self
pub fn Context::from_array(Array[Name]) -> Self
```

`from_array` copies the array, so later changes to the array do not affect the
context.

### `Context::extend_with`

`Context::extend_with` returns the context with one more name at the inner end.

```mbti
#alias(extend, deprecated)
pub fn Context::extend_with(Self, Name) -> Self
```

The original context is unchanged. The call copies the names, so it costs
$O(n)$ for a context of length $n$.

### `Context::contains`, `Context::length`, `Context::to_array`, `Context::equal`

These methods query a context.

```mbti
pub fn Context::contains(Self, Name) -> Bool
pub fn Context::length(Self) -> Int
pub fn Context::to_array(Self) -> Array[Name]
pub fn Context::equal(Self, Self) -> Bool
```

`contains` is a linear search. `to_array` returns a fresh array, outermost
name first; changing it does not change the context. `equal` is the promoted
`Eq` implementation.

```moonbit
test "contexts grow at the inner end" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let ctx = @core.Context::empty().extend_with(x).extend_with(y)
  assert_eq(ctx.length(), 2)
  assert_true(ctx.contains(y))
  assert_eq(ctx.to_array(), [x, y])
  assert_true(ctx == @core.Context::from_array([x, y]))
}
```

### `Telescope`

`Telescope[T]` is a sequence of binders, each with an annotation of type `T`,
in dependency order.

```mbti
type Telescope[T]
```

In a telescope $x_1 : A_1, \dots, x_n : A_n$ the annotation $A_i$ may refer to
$x_1, \dots, x_{i-1}$. `Telescope` records the order; it does not check what
the annotations mention. The type is abstract: read a telescope with `length`
and `to_array`.

### `Telescope::empty`, `Telescope::extend_with`, `Telescope::length`, `Telescope::to_array`

These functions build and read a telescope.

```mbti
pub fn[T] Telescope::empty() -> Self[T]
#alias(extend, deprecated)
pub fn[T] Telescope::extend_with(Self[T], Name, T) -> Self[T]
pub fn[T] Telescope::length(Self[T]) -> Int
pub fn[T] Telescope::to_array(Self[T]) -> Array[(Name, T)]
```

`extend_with` appends one binder and returns a new telescope; `to_array`
returns a fresh array of the entries, first binder first, and changing it does
not change the telescope.

```moonbit
test "telescopes keep binder order" {
  let a = @core.Name::new("A")
  let x = @core.Name::new("x")
  let tele : @core.Telescope[String] = @core.Telescope::empty()
    .extend_with(a, "Type")
    .extend_with(x, "A")
  assert_eq(tele.length(), 2)
  assert_eq(tele.to_array(), [(a, "Type"), (x, "A")])
}
```

## Renamings

### `Renaming`

`Renaming` is a finite map from names to names; names outside its domain are
left unchanged.

```mbti
type Renaming derive(Eq, @debug.Debug)
```

A renaming $\rho$ denotes the total function
$\rho(n) = m$ if $(n, m)$ is an entry and $\rho(n) = n$ otherwise. It is
applied simultaneously: the image of a name is never renamed again. A renaming
need not be injective. The type is abstract, so the only way to build a
renaming is through the functions below, and each name has at most one entry.
Equality (`Renaming::equal`) compares the entry lists, so two renamings that
denote the same function can still be different values.

### `Renaming::empty`, `Renaming::singleton`, `Renaming::set`

These functions build renamings.

```mbti
pub fn Renaming::empty() -> Self
pub fn Renaming::singleton(Name, Name) -> Self
pub fn Renaming::set(Self, Name, Name) -> Self
```

`set(from, to_)` adds the entry `from ↦ to_`, replacing an existing image of
`from` in place.

### `Renaming::apply`

`Renaming::apply` returns the image of a name.

```mbti
pub fn Renaming::apply(Self, Name) -> Name
```

### `Renaming::length`, `Renaming::to_array`

These methods read the entries of a renaming.

```mbti
pub fn Renaming::length(Self) -> Int
pub fn Renaming::to_array(Self) -> Array[(Name, Name)]
```

`length` is the number of names in the domain. `to_array` returns the entries
`(from, to_)` as a fresh array, in the order the names were first added;
changing the array does not change the renaming. An entry may map a name to
itself, so `length` can count names that `apply` leaves unchanged.

```moonbit
test "renaming entries are read through a copy" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let r = @core.Renaming::singleton(x, y).set(y, z).set(x, z)
  assert_eq(r.length(), 2)
  let entries = r.to_array()
  assert_eq(entries, [(x, z), (y, z)])
  entries.push((z, x))
  assert_eq(r.length(), 2)
  assert_eq(r.apply(z), z)
}
```

### `Renaming::without`

`Renaming::without` removes a name from the domain.

```mbti
pub fn Renaming::without(Self, Name) -> Self
```

This is the operation a binder performs: under a binder for `x`, free
occurrences of `x` are no longer the `x` of the renaming.

### `Renaming::support`, `Renaming::targets`

These methods return the names a renaming mentions.

```mbti
pub fn Renaming::support(Self) -> @hashset.HashSet[Name]
pub fn Renaming::targets(Self) -> @hashset.HashSet[Name]
```

`support` contains every source and every target of an entry; `targets`
contains only the targets. Capture-avoiding operations use them to choose
fresh binder names.

### `Renaming::then`

`Renaming::then` composes two renamings, applying `self` first.

```mbti
pub fn Renaming::then(Self, Self) -> Self
```

For every name $n$, `r.then(s).apply(n) == s.apply(r.apply(n))`.

```moonbit
test "renamings compose in application order" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let r = @core.Renaming::singleton(x, y)
  let s = @core.Renaming::singleton(y, z)
  let both = r.then(s)
  assert_eq(both.apply(x), z)
  assert_eq(both.apply(y), z)
  assert_eq(both.without(x).apply(x), x)
  assert_true(r.support().contains(x))
  assert_false(r.targets().contains(x))
}
```

### `Renaming::equal`

`Renaming::equal` compares two renamings entry by entry.

```mbti
pub fn Renaming::equal(Self, Self) -> Bool
```

It is the promoted `Eq` implementation; use `==` in new code.

## Deprecated

| Deprecated | Replacement |
| --- | --- |
| `Context::extend` | `Context::extend_with` |
| `Telescope::extend` | `Telescope::extend_with` |

The fields `Context::names`, `Telescope::entries` and `Renaming::entries`
are no longer public; use `to_array`, `length`, `contains` and
`apply` instead.

`extend` became a reserved word in MoonBit 0.10, so the methods were renamed.
The old names remain as deprecated aliases. The method forms `not_equal`,
`op_lt`, `op_le`, `op_gt`, `op_ge`, `hash_combine` and `to_repr` on these types
are hidden and deprecated; use the operators `!=`, `<`, `<=`, `>`, `>=`, the
`Hash` trait and `Repr(x)` instead.
