# substitution API

## Purpose

The `substitution` package replaces free variables by terms without capturing
variables. `Substitution[T]` works on `@syntax.Term[T]`;
`GenericSubstitution[N]` works on any AST that implements
`@syntax.BindingSyntax`. Both are finite, simultaneous and immutable: they
are abstract types, every operation returns a new value, and every method
that returns an array returns a fresh copy.

`Substitution::apply`, `Substitution::then` and
`GenericSubstitution::apply_once` are stack-safe in the nesting depth of the
term and of the replacements: they keep pending work in a heap array and use
a constant amount of host stack, so terms nested 100 000 levels deep are
handled on every backend. Formatting such a term with `Debug` is not
stack-safe; see the [syntax API](syntax.md).

The definition of capture-avoiding substitution and the proofs of its laws
are in the [substitution design](../design/substitution.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

## Substitutions on `Term`

### `Substitution`

`Substitution[T]` is a finite map from names to replacement terms.

```mbti
type Substitution[T]
```

It denotes the map $\sigma$ with $\sigma(x) = s$ for an entry $(x, s)$ and
$\sigma(x) = x$ (the variable itself) for every other name. The type is
abstract: the entries cannot be reached from outside the package, so the
functions below are the only way to build a substitution, and each name has
at most one entry.

Replacement terms are stored and returned as they are, not copied: `get`,
`to_array` and `apply` return terms that share structure with the terms
passed to `singleton` and `set`. `Term` is a plain enum whose `Apply`
arguments are an `Array`, so treat terms as immutable values; changing the
argument array of a term in place would also change every substitution that
holds it.

### `Substitution::empty`, `Substitution::singleton`, `Substitution::set`

These functions build substitutions.

```mbti
pub fn[T] Substitution::empty() -> Self[T]
pub fn[T] Substitution::singleton(@core.Name, @syntax.Term[T]) -> Self[T]
pub fn[T] Substitution::set(Self[T], @core.Name, @syntax.Term[T]) -> Self[T]
```

`set(x, s)` adds $x \mapsto s$, replacing an existing entry for `x` in place.

### `Substitution::get`

`Substitution::get` returns the replacement for a name, if any.

```mbti
pub fn[T] Substitution::get(Self[T], @core.Name) -> @syntax.Term[T]?
```

### `Substitution::length`, `Substitution::to_array`

These methods read the entries of a substitution.

```mbti
pub fn[T] Substitution::length(Self[T]) -> Int
pub fn[T] Substitution::to_array(Self[T]) -> Array[(@core.Name, @syntax.Term[T])]
```

`length` is the number of names in the domain. `to_array` returns the entries
`(x, s)` as a fresh array, in the order the names were first added; changing
the array does not change the substitution.

```moonbit
test "substitution entries are read through a copy" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let s : @substitution.Substitution[Int] = @substitution.Substitution::singleton(
    x,
    Value(1),
  ).set(y, Value(2))
  let entries = s.to_array()
  assert_eq(entries, [(x, Value(1)), (y, Value(2))])
  entries.push((x, Value(3)))
  assert_eq(s.length(), 2)
  assert_eq(s.get(x), Some(@syntax.Value(1)))
}
```

### `Substitution::without`, `Substitution::restrict`

These methods shrink the domain of a substitution.

```mbti
pub fn[T] Substitution::without(Self[T], @core.Name) -> Self[T]
pub fn[T] Substitution::restrict(Self[T], @hashset.HashSet[@core.Name]) -> Self[T]
```

`without(x)` drops the entry for `x`, which is what a binder for `x` does.
`restrict(names)` keeps only the entries whose name is in `names`.

```moonbit
test "build and shrink substitutions" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let s : @substitution.Substitution[Int] = @substitution.Substitution::singleton(
    x,
    Value(1),
  ).set(y, Value(2))
  assert_eq(s.get(x), Some(@syntax.Value(1)))
  assert_eq(s.without(x).get(x), None)
  assert_eq(s.restrict(@hashset.HashSet([y])).get(x), None)
  assert_eq(s.restrict(@hashset.HashSet([y])).get(y), Some(@syntax.Value(2)))
}
```

### `Substitution::apply`

`Substitution::apply` replaces the free variables of a term simultaneously,
renaming binders to avoid capture.

```mbti
pub fn[T] Substitution::apply(Self[T], @syntax.Term[T]) -> @syntax.Term[T]
```

Every free occurrence of a name `x` in the domain is replaced by its
replacement; nothing is substituted inside an inserted replacement. Under
`Bind(y, body)` the entry for `y` is ignored. When a replacement that is
actually inserted into `body` has `y` free, the binder is renamed to a fresh
name first, so free variables of replacements stay free. The result is
determined up to the choice of fresh names, which is deterministic.

```moonbit
test "substitution avoids capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let term : @syntax.Term[Int] = Bind(y, Apply(Variable(x), [Variable(y)]))
  let result = @substitution.Substitution::singleton(x, Variable(y)).apply(term)
  let y1 = @core.Name::new("y_1")
  let expected : @syntax.Term[Int] = Bind(y1, Apply(Variable(y), [Variable(y1)]))
  assert_eq(result, expected)
}
```

### `Substitution::then`

`Substitution::then` composes two substitutions, applying `self` first.

```mbti
pub fn[T] Substitution::then(Self[T], Self[T]) -> Self[T]
```

`s.then(t)` maps each `x` in the domain of `s` to `t.apply(s(x))`, and each
other `x` in the domain of `t` to `t(x)`. For every term,
`s.then(t).apply(term)` is alpha-equivalent to `t.apply(s.apply(term))`.

```moonbit
test "composition agrees with sequential application" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let first : @substitution.Substitution[Int] = @substitution.Substitution::singleton(
    x,
    Variable(y),
  )
  let second = @substitution.Substitution::singleton(y, Value(42))
  let term : @syntax.Term[Int] = Apply(Variable(x), [Variable(y)])
  let both = first.then(second)
  assert_true(
    @syntax.alpha_equal(both.apply(term), second.apply(first.apply(term))),
  )
  assert_eq(both.apply(term), Apply(Value(42), [Value(42)]))
}
```

### `from_renaming`

`from_renaming` turns a renaming into a substitution on a given set of names.

```mbti
pub fn[T] from_renaming(Array[@core.Name], @core.Renaming) -> Substitution[T]
```

The result maps each listed name `x` with `renaming.apply(x) != x` to
`Variable(renaming.apply(x))`. When the free variables of a term are among
the listed names, applying the result is alpha-equivalent to
`term.rename_free(renaming)`.

```moonbit
test "a renaming as a substitution" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let s : @substitution.Substitution[Int] = @substitution.from_renaming(
    [x],
    @core.Renaming::singleton(x, y),
  )
  assert_eq(s.apply(Variable(x)), Variable(y))
}
```

## Substitutions on binding-aware ASTs

### `GenericSubstitution`

`GenericSubstitution[N]` is a finite map from names to nodes of a downstream
AST `N`.

```mbti
type GenericSubstitution[N]
```

Like `Substitution`, the type is abstract and has at most one entry per name.
Replacement nodes are stored and returned without copying.

### `GenericSubstitution::empty`, `GenericSubstitution::singleton`, `GenericSubstitution::set`, `GenericSubstitution::get`, `GenericSubstitution::without`, `GenericSubstitution::length`, `GenericSubstitution::to_array`

These functions build and query generic substitutions; they behave exactly
like their `Substitution` counterparts.

```mbti
pub fn[N] GenericSubstitution::empty() -> Self[N]
pub fn[N] GenericSubstitution::singleton(@core.Name, N) -> Self[N]
pub fn[N] GenericSubstitution::set(Self[N], @core.Name, N) -> Self[N]
pub fn[N] GenericSubstitution::get(Self[N], @core.Name) -> N?
pub fn[N] GenericSubstitution::without(Self[N], @core.Name) -> Self[N]
pub fn[N] GenericSubstitution::length(Self[N]) -> Int
pub fn[N] GenericSubstitution::to_array(Self[N]) -> Array[(@core.Name, N)]
```

### `GenericSubstitution::apply_once`

`GenericSubstitution::apply_once` applies the substitution to a node in one
simultaneous, capture-avoiding pass.

```mbti
pub fn[N : @syntax.BindingSyntax] GenericSubstitution::apply_once(Self[N], N) -> N
```

The algorithm is the one of `Substitution::apply`, run through
`BindingSyntax::project` and rebuilt with `variable`, `apply` and `bind`.
`Opaque` nodes are returned unchanged. "Once" means that inserted
replacements are not visited again: substituting $x \mapsto y$ and
$y \mapsto 2$ in $x + y$ gives $y + 2$, not $2 + 2$.

```moonbit
test "generic substitution on Term" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let s = @substitution.GenericSubstitution::singleton(x, @syntax.Term::Variable(y))
    .set(y, @syntax.Value(2))
  let term : @syntax.Term[Int] = Apply(Variable(x), [Variable(y)])
  assert_eq(s.apply_once(term), Apply(Variable(y), [Value(2)]))
}
```

On `Term[T]`, `apply_once` agrees with `Substitution::apply`. For a
downstream AST see the [adapter tutorial](../tutorial/adapter.md).

## Removed fields

The field `entries` of `Substitution` and of `GenericSubstitution` is no
longer public. Read a substitution with `get`, `length` and `to_array`.
