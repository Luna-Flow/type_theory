# debruijn API

## Purpose

The `debruijn` package represents bound variables by De Bruijn indices:
`Bound(i)` refers to the binder `i` levels up. It converts from and to named
syntax, checks scope, shifts and substitutes indices, and implements
leftmost-outermost beta reduction without any renaming. Free variables stay
named.

The definitions of shifting and instantiation, with derivations of their
properties, are in the [debruijn design](../design/debruijn.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/debruijn",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

## Terms and errors

### `DbTerm`

`DbTerm[T]` is lambda syntax with nameless binders.

```mbti
pub(all) enum DbTerm[T] {
  Value(T)
  Free(@core.Name)
  Bound(Int)
  Apply(DbTerm[T], Array[DbTerm[T]])
  Bind(DbTerm[T])
} derive(Eq, @debug.Debug)
```

- `Value(v)` is a domain constant, opaque as in `@syntax.Term`.
- `Free(x)` is a free variable, kept by name.
- `Bound(i)` refers to the `i`-th enclosing `Bind`, counting from 0 for the
  innermost.
- `Apply(head, args)` is n-ary application, read as a curried spine.
- `Bind(body)` is a binder; its variable is `Bound(0)` in `body`.

A term is *well scoped* when every `Bound(i)` lies under more than `i`
binders. Because binders carry no names, `==` (`DbTerm::equal`) on
well-scoped terms is alpha-equivalence.

### `DbTerm::equal`

`DbTerm::equal` compares two terms structurally.

```mbti
pub fn[T : Eq] DbTerm::equal(Self[T], Self[T]) -> Bool
```

### `ScopeError`, `ScopeError::equal`

`ScopeError` describes an index that does not refer to a binder.

```mbti
pub(all) enum ScopeError {
  UnboundIndex(index~ : Int, depth~ : Int)
  NegativeIndex(index~ : Int)
  NegativeShift(index~ : Int, delta~ : Int, cutoff~ : Int)
} derive(Eq, @debug.Debug)
pub fn ScopeError::equal(Self, Self) -> Bool
```

- `UnboundIndex(index, depth)`: `Bound(index)` occurs under only `depth`
  binders.
- `NegativeIndex(index)`: a negative index.
- `NegativeShift(index, delta, cutoff)`: shifting the free `Bound(index)` by
  `delta` would move it below `cutoff`, the effective cutoff at the
  occurrence, where it would be captured by an enclosing binder or become
  negative.

## Conversion and validation

### `from_named`

`from_named` converts named syntax to De Bruijn syntax.

```mbti
pub fn[T] from_named(@syntax.Term[T]) -> DbTerm[T]
```

A variable bound by an enclosing `Bind` becomes `Bound(i)`, where `i` counts
the binders between the occurrence and its binder (the nearest binder of that
name wins). Free variables become `Free`. The result is always well scoped,
and alpha-equivalent named terms give equal results.

### `to_named`

`to_named` converts De Bruijn syntax back to named syntax with deterministic
binder names.

```mbti
pub fn[T] to_named(DbTerm[T]) -> Result[@syntax.Term[T], ScopeError]
```

Binders are named `x`, `x_1`, `x_2`, …: each one gets the first name of that
sequence that is neither a free name of the term nor the name of an enclosing
binder. Returns `Err(NegativeIndex)` or `Err(UnboundIndex)` for an ill-scoped
term. For a well-scoped `d`, `from_named(to_named(d))` is `d`; for a named
`t`, `to_named(from_named(t))` is alpha-equivalent to `t`.

```moonbit
test "named and nameless round trip" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let named : @syntax.Term[Int] = Bind(y, Apply(Variable(y), [Variable(x)]))
  let db = @debruijn.from_named(named)
  assert_eq(db, Bind(Apply(Bound(0), [Free(x)])))
  match @debruijn.to_named(db) {
    Ok(back) => {
      assert_true(@syntax.alpha_equal(back, named))
      assert_true(back is Bind(binder, _) && binder.text() == "x_1")
    }
    Err(_) => fail("well scoped")
  }
}
```

The binder becomes `x_1` because `x` is a free name of the term.

### `validate`

`validate` checks that every bound index refers to an enclosing binder.

```mbti
pub fn[T] validate(DbTerm[T]) -> Result[Unit, ScopeError]
```

Returns `Ok(())` for a well-scoped term and otherwise the first error found
in pre-order.

```moonbit
test "dangling index" {
  let bad : @debruijn.DbTerm[Int] = Bind(Bound(1))
  assert_eq(@debruijn.validate(bad), Err(UnboundIndex(index=1, depth=1)))
  let good : @debruijn.DbTerm[Int] = Bind(Bound(0))
  assert_eq(@debruijn.validate(good), Ok(()))
}
```

## Index operations

### `shift`

`shift` adds `delta` to every index that is free relative to a cutoff.

```mbti
pub fn[T] shift(DbTerm[T], Int, Int) -> Result[DbTerm[T], ScopeError]
```

`shift(t, delta, cutoff)` is the operation $\uparrow^{delta}_{cutoff}$:
under `k` binders, an index `i >= cutoff + k` becomes `i + delta`, and smaller
indices are left alone. The shift is defined when no such index falls below
the cutoff, that is, there is no `i >= cutoff + k` with
`i + delta < cutoff + k`. Returns `Err(NegativeShift)` if an index would fall
below the cutoff, where it would be captured by an enclosing binder or become
negative, and `Err(NegativeIndex)` if the input contains a negative index.

### `substitute_bound`

`substitute_bound` replaces a free index by a term.

```mbti
pub fn[T] substitute_bound(DbTerm[T], Int, DbTerm[T]) -> Result[DbTerm[T], ScopeError]
```

`substitute_bound(t, j, s)` is $[j \mapsto s]\,t$: under `k` binders,
`Bound(j + k)` is replaced by `s` shifted up by `k`, so that the free indices
of `s` keep pointing at the same binders. Other indices are unchanged; the
binder count of the result is not adjusted. Returns `Err(NegativeIndex)` for
a negative `j` or a negative index in `t`. It does not check for unbound
indices; use `validate` for that.

### `instantiate`

`instantiate` opens a binder body with an argument.

```mbti
pub fn[T] instantiate(DbTerm[T], DbTerm[T]) -> Result[DbTerm[T], ScopeError]
```

`instantiate(body, arg)` computes
$\uparrow^{-1}_0\big([0 \mapsto \uparrow^{1}_0 arg]\,body\big)$, the result
of the beta step $(\lambda.\,body)\,arg$. On well-scoped input it never
returns an error.

```moonbit
test "instantiate a binder body" {
  let y = @core.Name::new("y")
  // body of λ. λ. 1 0, i.e. λ. (outer variable) applied to (inner variable)
  let body : @debruijn.DbTerm[Int] = Bind(Apply(Bound(1), [Bound(0)]))
  assert_eq(
    @debruijn.instantiate(body, Free(y)),
    Ok(Bind(Apply(Free(y), [Bound(0)]))),
  )
  let open_term : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(1)]))
  assert_eq(
    @debruijn.shift(open_term, 2, 0),
    Ok(Bind(Apply(Bound(0), [Bound(3)]))),
  )
  // shifting λ. (free 0) down would capture the free index
  let captured : @debruijn.DbTerm[Int] = Bind(Bound(1))
  assert_eq(
    @debruijn.shift(captured, -1, 0),
    Err(NegativeShift(index=1, delta=-1, cutoff=1)),
  )
  let under_binder : @debruijn.DbTerm[Int] = Bind(Bound(1))
  assert_eq(
    @debruijn.substitute_bound(under_binder, 0, Bound(5)),
    Ok(Bind(Bound(6))),
  )
}
```

## Reduction

### `DbStepResult`, `DbStepResult::equal`

`DbStepResult[T]` is the outcome of one De Bruijn reduction attempt.

```mbti
pub(all) enum DbStepResult[T] {
  NoStep
  Reduced(before~ : DbTerm[T], after~ : DbTerm[T], rule~ : @rewrite.RuleName, path~ : @rewrite.ReductionPath)
  ScopeFailure(ScopeError)
} derive(Eq, @debug.Debug)
pub fn[T : Eq] DbStepResult::equal(Self[T], Self[T]) -> Bool
```

`NoStep` and `Reduced` have the meaning of `@rewrite.StepResult`; the rule
name is always `"beta"`. `ScopeFailure` reports that the input is ill
scoped: `reduce_once` validates the whole term before searching for a redex,
and the error is the first one `validate` finds. No step is taken in that
case.

### `reduce_once`

`reduce_once` performs one leftmost-outermost beta step.

```mbti
pub fn[T] reduce_once(DbTerm[T]) -> DbStepResult[T]
```

A redex is `Apply(Bind(body), [a, ..rest])`; it becomes
`instantiate(body, a)`, applied to `rest` if `rest` is not empty. An empty
application `Apply(h, [])` is read as `h`, so a head wrapped in empty
applications, as in `Apply(Apply(Bind(body), []), [a])`, still forms a redex;
`Apply(Bind(body), [])` alone has no argument and is not one. The search
order is the root, then the head, then the arguments from left to right, and
binder bodies are entered.

`reduce_once` validates the whole term first, as `validate` does: an
ill-scoped term gives `ScopeFailure` with the first error in pre-order,
wherever the bad index is, for example `ScopeFailure(NegativeIndex(index=-1))`
for `Bind(Bound(-1))` and `ScopeFailure(UnboundIndex(index=5, depth=1))` for
`(λ. 5) 1`. A well-scoped term never gives `ScopeFailure`.

### `DbNormalizationResult`, `DbNormalizationResult::equal`

`DbNormalizationResult[T]` is the outcome of bounded De Bruijn normalization.

```mbti
pub(all) enum DbNormalizationResult[T] {
  NormalForm(term~ : DbTerm[T], steps~ : Int)
  StepLimitReached(term~ : DbTerm[T], steps~ : Int)
  ScopeFailure(term~ : DbTerm[T], error~ : ScopeError, steps~ : Int)
} derive(Eq, @debug.Debug)
pub fn[T : Eq] DbNormalizationResult::equal(Self[T], Self[T]) -> Bool
```

`ScopeFailure` carries the term that was found ill scoped, the error and
the number of steps taken before it; `normalize` reports it only for its
input, with `steps=0`.

### `normalize`

`normalize` repeats `reduce_once` until no step applies, a step fails, or a
step limit is reached.

```mbti
pub fn[T] normalize(DbTerm[T], Int) -> DbNormalizationResult[T]
```

It has the step-count contract of `@rewrite.normalize`: at most `max_steps`
steps, and one extra step attempt to classify the final term. It validates
the input once: an ill-scoped term gives `ScopeFailure(term, error, steps=0)`
without any step. Reducts of a well-scoped term are well scoped (see the
[debruijn design](../design/debruijn.md)), so the later steps are not
validated again, and the result is `ScopeFailure` exactly when the input is
ill scoped.

```moonbit
test "nameless beta reduction" {
  let f = @core.Name::new("f")
  // λ. f ((λ. 0) 7)
  let term : @debruijn.DbTerm[Int] = Bind(
    Apply(Free(f), [Apply(Bind(Bound(0)), [Value(7)])]),
  )
  match @debruijn.reduce_once(term) {
    Reduced(after~, path~, rule~, ..) => {
      assert_eq(after, Bind(Apply(Free(f), [Value(7)])))
      assert_eq(path.to_array(), [@rewrite.BinderBody, @rewrite.ApplyArgument(0)])
      inspect(rule.value(), content="beta")
    }
    _ => fail("expected a beta step")
  }
  assert_eq(
    @debruijn.normalize(term, 10),
    NormalForm(term=Bind(Apply(Free(f), [Value(7)])), steps=1),
  )
}
```
