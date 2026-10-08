# utlc/nbe API

## Purpose

The `utlc/nbe` package normalizes untyped De Bruijn terms by evaluation:
`eval` interprets a term in a lazy semantic domain, `quote` reads a semantic
value back as a beta-normal term, and `normalize` does both. Every phase
consumes *fuel*, so divergent terms end with `FuelExhausted` instead of
running forever.

The semantic domain and the correctness argument are described in the
[utlc/nbe design](../../design/utlc/nbe.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/debruijn",
  "Luna-Flow/type_theory/utlc/nbe",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

The default alias of the package is `@nbe`.

## Fuel

Fuel is a step budget measured in units: every evaluation of a term node,
every forcing of a delayed value and every readback of a value costs one
unit. All results report `consumed`, the units used. A call with fuel `<= 0`
returns `FuelExhausted(consumed=0)` without doing anything (`quote` first
rejects a negative level). The result of a
call does not depend on the fuel beyond what it consumed: if a call with fuel
$f$ returns a normal form after consuming $c$ units, every call with fuel at
least $c$ returns the same result.

## Semantic values

### `Semantic`

`Semantic[T]` is an opaque semantic value.

```mbti
pub struct Semantic[T] {
  inner : SemanticInner[T]
}

type SemanticInner[T]
```

A semantic value is a constant, a closure (a binder body with its
environment), a delayed argument, or a neutral value (a free variable, a
variable at a quote level, or a neutral value applied to an argument). The
representation is private; values are produced by `eval` and the `reflect_*`
functions and consumed by `quote`.

### `reflect_free`

`reflect_free` turns a free name into a neutral semantic value.

```mbti
pub fn[T] reflect_free(@core.Name) -> Semantic[T]
```

Quoting it gives `Free(name)`.

### `reflect_level`

`reflect_level` turns a quote level into a neutral semantic variable.

```mbti
pub fn[T] reflect_level(Int) -> Semantic[T]?
```

Returns `None` for a negative level. Quoting the variable of level `l` at
depth `n > l` gives `Bound(n - l - 1)`.

```moonbit
test "reflect and quote neutral values" {
  let y = @core.Name::new("y")
  let free : @nbe.Semantic[Int] = @nbe.reflect_free(y)
  assert_true(@nbe.quote(free, 0, 10) is Quoted(term=Free(_), ..))
  match @nbe.reflect_level(0) {
    Some(v) => {
      let value : @nbe.Semantic[Int] = v
      // the variable of level 0, seen from depth 2, is index 1
      assert_true(@nbe.quote(value, 2, 10) is Quoted(term=Bound(1), ..))
    }
    None => fail("level 0 is valid")
  }
  let negative : @nbe.Semantic[Int]? = @nbe.reflect_level(-1)
  assert_true(negative is None)
}
```

## Evaluation and readback

### `EvaluationResult`

`EvaluationResult[T]` is the outcome of `eval`.

```mbti
pub(all) enum EvaluationResult[T] {
  Evaluated(value~ : Semantic[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
}
```

### `eval`

`eval` evaluates a closed De Bruijn term to weak head form in the lazy
semantic domain.

```mbti
pub fn[T] eval(@debruijn.DbTerm[T], Int) -> EvaluationResult[T]
```

The term must be well scoped (free names are allowed); otherwise the result
is `ScopeFailure` with `consumed=0`. Evaluation is call by name: arguments are
delayed and evaluated only when needed, and evaluation stops at a closure or
a neutral value without entering binders.

### `QuoteResult`

`QuoteResult[T]` is the outcome of `quote`.

```mbti
pub(all) enum QuoteResult[T] {
  Quoted(term~ : @debruijn.DbTerm[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
}
```

### `quote`

`quote` reads a semantic value back as a beta-normal De Bruijn term.

```mbti
pub fn[T] quote(Semantic[T], Int, Int) -> QuoteResult[T]
```

`quote(value, level, fuel)` reads `value` back under `level` binders. A
closure is read back by applying it to a fresh variable of the current level
and reading the result under one more binder; neutral applications are read
back argument by argument, which forces delayed arguments. Use `level = 0`
for values from `eval`. A negative `level`, or a level variable that is not
below `level`, gives `ScopeFailure(NegativeIndex)`.

```moonbit
test "eval then quote" {
  // (λ. 0) (λ. 0)
  let id : @debruijn.DbTerm[Int] = Bind(Bound(0))
  let term : @debruijn.DbTerm[Int] = Apply(id, [id])
  match @nbe.eval(term, 100) {
    Evaluated(value~, ..) =>
      assert_true(@nbe.quote(value, 0, 100) is Quoted(term=Bind(Bound(0)), ..))
    _ => fail("closed and small")
  }
}
```

## Normalization

### `NbeResult`, `NbeResult::equal`

`NbeResult[T]` is the outcome of `normalize`.

```mbti
pub(all) enum NbeResult[T] {
  NormalForm(term~ : @debruijn.DbTerm[T], consumed~ : Int)
  FuelExhausted(consumed~ : Int)
  ScopeFailure(error~ : @debruijn.ScopeError, consumed~ : Int)
} derive(Eq, @debug.Debug)
pub fn[T : Eq] NbeResult::equal(Self[T], Self[T]) -> Bool
```

### `normalize`

`normalize` computes the beta normal form of a well-scoped De Bruijn term
within a fuel budget.

```mbti
pub fn[T] normalize(@debruijn.DbTerm[T], Int) -> NbeResult[T]
```

It validates the term, evaluates it and quotes the result at level 0, with
one shared budget. `NormalForm(t, c)`: `t` is the beta normal form, reached
with `c` units. `FuelExhausted(c)`: the budget ran out; the term may diverge
or may need more fuel. `ScopeFailure`: the input has a dangling or negative
index. The fuel test comes first, so an ill-scoped term with fuel `<= 0`
gives `FuelExhausted(consumed=0)`, not `ScopeFailure`.

Applications in the result are unary: a normal form $f\,a\,b$ is returned as
`Apply(Apply(f, [a]), [b])`, while `@debruijn.normalize` keeps the n-ary
spine `Apply(f, [a, b])` of the input. An empty application `Apply(h, [])`
evaluates to the value of `h`, so it disappears from the result, while the
small-step reducers keep it and do not reduce through it. The two
normalizers agree after spines are flattened, for terms without empty
applications.

```moonbit
test "lazy evaluation skips an unused divergent argument" {
  let w : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0)]))
  let omega : @debruijn.DbTerm[Int] = Apply(w, [w])
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Value(7)), [omega])
  assert_true(@nbe.normalize(term, 100) is NormalForm(term=Value(7), ..))
  assert_true(@nbe.normalize(omega, 100) is FuelExhausted(_))
}
```
