# syntax API

## Purpose

The `syntax` package defines named syntax with binders: the generic term type
`Term[T]`, the analyses on it (free variables, all names, alpha-equivalence),
renaming, and the open trait `BindingSyntax` through which a downstream AST
gets the same analyses and the generic substitution and rewriting of the
other packages.

The definitions behind these functions, and the proofs of their laws, are in
the [syntax design](../design/syntax.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

## Terms

### `Term`

`Term[T]` is named syntax with domain values, variables, n-ary application
and single-variable binding.

```mbti
pub(all) enum Term[T] {
  Value(T)
  Variable(@core.Name)
  Apply(Term[T], Array[Term[T]])
  Bind(@core.Name, Term[T])
} derive(Eq, @debug.Debug)
```

- `Value(v)` is a domain constant. Its payload `T` is opaque: it is treated as
  closed, so no analysis looks inside it.
- `Variable(x)` is an occurrence of the name `x`.
- `Apply(head, args)` applies `head` to a sequence of arguments. The lambda
  calculus packages read it as the curried application
  $head\ a_1\ \cdots\ a_n$.
- `Bind(x, body)` binds `x` in `body`. In the lambda calculus it is
  $\lambda x.\,body$; a downstream language may read it as any one-variable
  binder.

`==` (`Term::equal`) is structural equality: binder names must match
literally. Use `alpha_equal` to compare terms up to renaming of bound
variables.

```moonbit
test "build the term λx. f x 1" {
  let x = @core.Name::new("x")
  let f = @core.Name::new("f")
  let term : @syntax.Term[Int] = Bind(
    x,
    Apply(Variable(f), [Variable(x), Value(1)]),
  )
  assert_true(term is Bind(_, Apply(_, [_, Value(1)])))
}
```

### `Term::equal`

`Term::equal` compares two terms structurally.

```mbti
pub fn[T : Eq] Term::equal(Self[T], Self[T]) -> Bool
```

It is the promoted `Eq` implementation. `λx.x` and `λy.y` are not `equal`.

### `Term::map_values`

`Term::map_values` applies a function to every domain value and keeps the
variables and binders.

```mbti
pub fn[T, U] Term::map_values(Self[T], (T) -> U) -> Self[U]
```

It is a functor map: `t.map_values(v => v)` is `t`, and mapping `f` then `g`
equals mapping `v => g(f(v))`. Free variables are unchanged.

```moonbit
test "map domain values" {
  let x = @core.Name::new("x")
  let term : @syntax.Term[Int] = Apply(Value(2), [Variable(x), Value(3)])
  let shown = term.map_values(v => v.to_string())
  assert_eq(shown, Apply(Value("2"), [Variable(x), Value("3")]))
}
```

## Analyses

### `free_variables`

`free_variables` returns the names that occur free in a term.

```mbti
pub fn[T] free_variables(Term[T]) -> @hashset.HashSet[@core.Name]
```

An occurrence of `x` is free when no enclosing `Bind(x, _)` binds it. Values
contribute no names. Cost: $O(n)$ set operations for a term of size $n$.

### `all_names`

`all_names` returns every name in a term: free variables, bound occurrences
and binder names.

```mbti
pub fn[T] all_names(Term[T]) -> @hashset.HashSet[@core.Name]
```

Use it as the "used" set when choosing a fresh name for a term.

```moonbit
test "free and all names" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let term : @syntax.Term[Int] = Bind(x, Apply(Variable(x), [Variable(z)]))
  let fv = @syntax.free_variables(term)
  assert_true(fv.contains(z))
  assert_false(fv.contains(x))
  assert_true(@syntax.all_names(term).contains(x))
  assert_false(@syntax.all_names(term).contains(y))
}
```

### `alpha_equal`

`alpha_equal` decides whether two terms are equal up to the names of bound
variables.

```mbti
pub fn[T : Eq] alpha_equal(Term[T], Term[T]) -> Bool
```

Values are compared with `==`, free variables by name, and bound variables by
the binder they refer to. The relation is an equivalence and is decided in
one simultaneous traversal of both terms.

```moonbit
test "alpha-equivalence ignores binder names" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let left : @syntax.Term[Int] = Bind(x, Apply(Variable(x), [Variable(z)]))
  let right : @syntax.Term[Int] = Bind(y, Apply(Variable(y), [Variable(z)]))
  assert_true(@syntax.alpha_equal(left, right))
  assert_false(left == right)
  let other : @syntax.Term[Int] = Bind(y, Apply(Variable(y), [Variable(y)]))
  assert_false(@syntax.alpha_equal(left, other))
}
```

## Renaming

### `Term::rename_free`

`Term::rename_free` applies a renaming to the free variables of a term,
renaming binders where necessary to avoid capture.

```mbti
pub fn[T] Term::rename_free(Self[T], @core.Renaming) -> Self[T]
```

Under `Bind(x, body)` the renaming loses its entry for `x`, because the bound
`x` is a different variable. If a remaining target of the renaming equals
`x`, the binder is renamed to a fresh name first. The result is
alpha-equivalent to the textbook capture-avoiding renaming.

```moonbit
test "rename a free variable without capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let term : @syntax.Term[Int] = Bind(y, Variable(x))
  let renamed = term.rename_free(@core.Renaming::singleton(x, y))
  let expected : @syntax.Term[Int] = Bind(@core.Name::new("y_1"), Variable(y))
  assert_eq(renamed, expected)
}
```

### `Term::alpha_rename_bound`

`Term::alpha_rename_bound` renames the occurrences of a variable that are
bound by an enclosing binder, refusing a target name that could be captured.

```mbti
pub fn[T] Term::alpha_rename_bound(Self[T], @core.Name, @core.Name) -> Self[T]?
```

Call it on the *body* of a binder: `body.alpha_rename_bound(from, to_)`
replaces the occurrences of `from` that are free in `body` (and therefore
bound by the enclosing `Bind(from, body)`) with `to_`. Inner binders named
`from` stop the renaming. The result is `None` when `to_` occurs anywhere in
`body`, and `Some(body)` when `from == to_`. On success,
`Bind(from, body)` and `Bind(to_, result)` are alpha-equivalent.

```moonbit
test "checked bound renaming" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let body : @syntax.Term[Int] = Bind(y, Variable(x))
  assert_true(body.alpha_rename_bound(x, y) is None)
  let expected : @syntax.Term[Int] = Bind(y, Variable(z))
  assert_eq(body.alpha_rename_bound(x, z), Some(expected))
}
```

## Binding-aware ASTs

### `BindingView`

`BindingView[N]` is the one-layer view of a node that generic algorithms
inspect.

```mbti
pub(all) enum BindingView[N] {
  Opaque
  Variable(@core.Name)
  Apply(N, Array[N])
  Bind(@core.Name, N)
}
```

`Opaque` marks a node with no variables inside, such as a literal. The other
cases mirror the constructors of `Term`, with the children left in the
downstream type `N`.

### `BindingSyntax`

`BindingSyntax` is the open trait that a downstream AST implements to use the
generic binding algorithms.

```mbti
pub(open) trait BindingSyntax {
  fn project(Self) -> BindingView[Self]
  fn variable(@core.Name) -> Self
  fn apply(Self, Array[Self]) -> Self
  fn bind(@core.Name, Self) -> Self
}
```

- `project(node)` tells the algorithms what the node is.
- `variable`, `apply` and `bind` rebuild nodes of each kind.

An implementation must make `project` and the three constructors agree:
`project(variable(x))` is `Variable(x)`, `project(apply(h, args))` is
`Apply(h, args)`, `project(bind(x, b))` is `Bind(x, b)`, and rebuilding a
projected `Apply` or `Bind` node gives back an equivalent node. An `Opaque`
node must not contain variables. The [adapter design](../design/adapter.md)
explains these laws; the [adapter tutorial](../tutorial/adapter.md) implements
them for a small AST.

Call the trait methods through the trait, for example
`@syntax.BindingSyntax::project(node)`.

### `impl BindingSyntax for Term`

`Term[T]` implements `BindingSyntax` with the obvious projection.

```mbti
pub impl[T] BindingSyntax for Term[T]
```

`Value` projects to `Opaque` and every other constructor to the case of the
same name, so the generic functions below agree with their `Term` versions on
`Term` values.

```moonbit
test "project a term" {
  let x = @core.Name::new("x")
  let term : @syntax.Term[Int] = Bind(x, Variable(x))
  match @syntax.BindingSyntax::project(term) {
    Bind(name, _) => assert_eq(name, x)
    _ => fail("expected a binder")
  }
}
```

### `generic_free_variables`, `generic_all_names`

These functions compute free variables and all names for any
`BindingSyntax` type.

```mbti
pub fn[N : BindingSyntax] generic_free_variables(N) -> @hashset.HashSet[@core.Name]
pub fn[N : BindingSyntax] generic_all_names(N) -> @hashset.HashSet[@core.Name]
```

On `Term[T]` they return the same sets as `free_variables` and `all_names`.

### `generic_alpha_rename_bound`

`generic_alpha_rename_bound` is `Term::alpha_rename_bound` for any
`BindingSyntax` type.

```mbti
pub fn[N : BindingSyntax] generic_alpha_rename_bound(N, @core.Name, @core.Name) -> N?
```

It returns `None` when the target name occurs in the node, and rebuilds the
renamed node through `variable`, `apply` and `bind`.

```moonbit
test "generic analyses on a term" {
  let x = @core.Name::new("x")
  let z = @core.Name::new("z")
  let term : @syntax.Term[Int] = Apply(Variable(x), [Bind(z, Variable(z))])
  assert_true(@syntax.generic_free_variables(term).contains(x))
  assert_false(@syntax.generic_free_variables(term).contains(z))
  let renamed = @syntax.generic_alpha_rename_bound(term, x, @core.Name::new("w"))
  assert_true(renamed is Some(Apply(Variable(_), [_])))
}
```

## Deprecated

| Deprecated | Replacement |
| --- | --- |
| `term.project()` | `@syntax.BindingSyntax::project(term)` |
| `Term::variable(name)` method form | `Term::Variable(name)` |
| `Term::apply(head, args)` method form | `Term::Apply(head, args)` |
| `Term::bind(name, body)` method form | `Term::Bind(name, body)` |
| `term.not_equal(other)` | `term != other` |
| `term.to_repr()` | `Repr(term)` or `@debug.to_string(term)` |

These method forms were implicit promotions of trait methods. They are kept
hidden and deprecated so that old callers still compile.
