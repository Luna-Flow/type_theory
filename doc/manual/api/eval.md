# eval API

## Purpose

The `eval` package names the usual reduction strategies and runs any rewrite
rule with one of them: one step, bounded normalization, or a full trace. It
is a thin layer over [rewrite](rewrite.md); the rule itself (beta, eta, a
domain simplification) is supplied by the caller.

The strategies are defined precisely in the [eval design](../design/eval.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/eval",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

The examples use the beta rule of `Luna-Flow/type_theory/utlc/lambda`
(alias `@lambda`), which you import as well.

## Strategies

### `Strategy`

`Strategy` selects where the next step is taken.

```mbti
pub(all) enum Strategy {
  NormalOrder
  ApplicativeOrder
  WeakHead
  FullNormal
} derive(Eq, @debug.Debug)
```

| Strategy | Next position | Enters binders and arguments |
| --- | --- | --- |
| `NormalOrder` | leftmost-outermost redex (`@rewrite.top_down_once`) | yes |
| `ApplicativeOrder` | leftmost-innermost redex (`@rewrite.bottom_up_once`) | yes |
| `WeakHead` | the root, else the head of an application, recursively | no |
| `FullNormal` | same as `NormalOrder` | yes |

`FullNormal` currently selects the same traversal as `NormalOrder`; it names
the intent "reduce to full normal form" and may diverge from `NormalOrder` if
another full-normalization traversal is added.

### `Strategy::equal`

`Strategy::equal` compares two strategies.

```mbti
pub fn Strategy::equal(Self, Self) -> Bool
```

It is the promoted `Eq` implementation; use `==` in new code.

## Running a strategy

### `reduce_once`

`reduce_once` performs at most one reduction step with a strategy.

```mbti
pub fn[T] reduce_once(@syntax.Term[T], @rewrite.RuleName, (@syntax.Term[T]) -> @syntax.Term[T]?, Strategy) -> @rewrite.StepResult[T]
```

The result follows the contract of `@rewrite.StepResult`: `Reduced` reports
one rewritten position and its path. For `NormalOrder`, `FullNormal` and
`ApplicativeOrder`, `NoStep` means the rule applies nowhere. For `WeakHead`,
`NoStep` means the rule applies neither at the root nor at any head position
of the application spine; the term is then in weak head normal form for the
rule, but may contain redexes under binders or in arguments.

With `@lambda.beta_rule`, a redex is an `Apply` with a non-empty argument
array whose head is a `Bind`, possibly wrapped in empty applications
`Apply(h, [])`, which are read as `h`. Every strategy therefore contracts
$(\lambda x.\,b)\,a$ in `Apply(Apply(Bind(x, b), []), [a])`, at the root.

```moonbit
test "weak head stops at a binder" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let id : @syntax.Term[Int] = Bind(y, Variable(y))
  let term : @syntax.Term[Int] = Bind(x, Apply(id, [Variable(z)]))
  let beta = @rewrite.RuleName::unsafe_new("beta")
  assert_true(@eval.reduce_once(term, beta, @lambda.beta_rule, WeakHead) is NoStep)
  match @eval.reduce_once(term, beta, @lambda.beta_rule, NormalOrder) {
    Reduced(after~, path~, ..) => {
      assert_eq(after, Bind(x, Variable(z)))
      assert_eq(path.to_array(), [@rewrite.BinderBody])
    }
    NoStep => fail("expected a step under the binder")
  }
}
```

### `evaluate`

`evaluate` normalizes a term by repeating `reduce_once` with one strategy.

```mbti
pub fn[T] evaluate(@syntax.Term[T], @rewrite.RuleName, (@syntax.Term[T]) -> @syntax.Term[T]?, Strategy, Int) -> @rewrite.NormalizationResult[T]
```

`evaluate(term, name, rule, strategy, max_steps)` is
`@rewrite.normalize(term, t => reduce_once(t, name, rule, strategy), max_steps)`,
with the same step-count contract: at most `max_steps` steps, and
`NormalForm` only for a term on which the strategy finds no step.

```moonbit
test "normal order finds a normal form that applicative order misses" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let w = @core.Name::new("w")
  let self_apply : @syntax.Term[Int] = Bind(w, Apply(Variable(w), [Variable(w)]))
  let omega : @syntax.Term[Int] = Apply(self_apply, [self_apply])
  let term : @syntax.Term[Int] = Apply(Bind(x, Variable(y)), [omega])
  let beta = @rewrite.RuleName::unsafe_new("beta")
  assert_eq(
    @eval.evaluate(term, beta, @lambda.beta_rule, NormalOrder, 10),
    NormalForm(term=Variable(y), steps=1),
  )
  assert_true(
    @eval.evaluate(term, beta, @lambda.beta_rule, ApplicativeOrder, 10)
    is StepLimitReached(..),
  )
}
```

### `trace`

`trace` normalizes like `evaluate` and records every step.

```mbti
pub fn[T] trace(@syntax.Term[T], @rewrite.RuleName, (@syntax.Term[T]) -> @syntax.Term[T]?, Strategy, Int) -> @rewrite.ReductionTrace[T]
```

It is `@rewrite.trace` with the step function of the strategy. Every
strategy reports its own input as `before`, so the trace satisfies the
chaining invariants of `@rewrite.ReductionTrace`.

```moonbit
test "trace a two-step reduction" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let k : @syntax.Term[Int] = Bind(x, Bind(y, Variable(x)))
  let term : @syntax.Term[Int] = Apply(k, [Value(1), Value(2)])
  let beta = @rewrite.RuleName::unsafe_new("beta")
  let run = @eval.trace(term, beta, @lambda.beta_rule, NormalOrder, 10)
  assert_eq(run.steps().length(), 2)
  assert_eq(run.result(), NormalForm(term=Value(1), steps=2))
}
```
