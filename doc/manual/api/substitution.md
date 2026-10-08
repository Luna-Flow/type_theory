# substitution API

## Purpose

The `substitution` package replaces free variables by terms without capturing
variables. `Substitution[T]` works on `@syntax.Term[T]`;
`GenericSubstitution[N]` works on any AST that implements
`@syntax.BindingSyntax`. Both are finite, simultaneous and immutable.

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
pub struct Substitution[T] {
  entries : Array[(@core.Name, @syntax.Term[T])]
}
```

It denotes the map $\sigma$ with $\sigma(x) = s$ for an entry $(x, s)$ and
$\sigma(x) = x$ (the variable itself) for every other name. The entries are
read-only outside the package; at most one entry exists per name.

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
pub struct GenericSubstitution[N] {
  entries : Array[(@core.Name, N)]
}
```

### `GenericSubstitution::empty`, `GenericSubstitution::singleton`, `GenericSubstitution::set`, `GenericSubstitution::get`, `GenericSubstitution::without`

These functions build and query generic substitutions; they behave exactly
like their `Substitution` counterparts.

```mbti
pub fn[N] GenericSubstitution::empty() -> Self[N]
pub fn[N] GenericSubstitution::singleton(@core.Name, N) -> Self[N]
pub fn[N] GenericSubstitution::set(Self[N], @core.Name, N) -> Self[N]
pub fn[N] GenericSubstitution::get(Self[N], @core.Name) -> N?
pub fn[N] GenericSubstitution::without(Self[N], @core.Name) -> Self[N]
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
