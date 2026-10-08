# rewrite API

## Purpose

The `rewrite` package applies a rewrite rule at one position of a term and
reports exactly what happened: the term before and after, the rule's name
and the path from the root to the rewritten position. Bounded
normalization and traces are built by repeating such single steps. Every
function has a `Term[T]` version and, where noted, a version for any
`@syntax.BindingSyntax` AST.

A *rule* is a function `(Term[T]) -> Term[T]?` that returns `Some(result)`
when it applies to a term as a whole and `None` otherwise. The traversal
functions decide *where* the rule is tried. The theory is in the
[rewrite design](../design/rewrite.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

## Rule names

### `RuleName`

`RuleName` is a non-empty identifier for a reduction rule.

```mbti
pub struct RuleName {
  value : String
} derive(Compare, Eq, Hash, @debug.Debug)
```

Rule names label steps in results and traces. They compare, order and hash
by their text; the order is that of `String`: shorter texts first, then by
UTF-16 code units.

### `RuleName::new`

`RuleName::new` validates and creates a rule name.

```mbti
pub fn RuleName::new(String) -> Result[Self, RuleNameError]
```

Returns `Err(RuleNameError::Empty)` for the empty string and `Ok(name)`
otherwise.

### `RuleName::unsafe_new`

`RuleName::unsafe_new` creates a rule name from a string known to be
non-empty.

```mbti
pub fn RuleName::unsafe_new(String) -> Self
```

Aborts on the empty string. Use it for literals such as `"beta"`, where the
invariant is evident; use `RuleName::new` for names that come from input.

### `RuleName::value`

`RuleName::value` returns the text of a rule name.

```mbti
pub fn RuleName::value(Self) -> String
```

### `RuleName::equal`, `RuleName::compare`, `RuleName::hash`

These methods are the promoted `Eq`, `Compare` and `Hash` implementations.

```mbti
pub fn RuleName::equal(Self, Self) -> Bool
pub fn RuleName::compare(Self, Self) -> Int
pub fn RuleName::hash(Self) -> Int
```

```moonbit
test "rule names" {
  assert_eq(@rewrite.RuleName::new(""), Err(@rewrite.RuleNameError::Empty))
  match @rewrite.RuleName::new("beta") {
    Ok(name) => inspect(name.value(), content="beta")
    Err(_) => fail("non-empty name rejected")
  }
  // shortlex order: shorter names first
  let eta = @rewrite.RuleName::unsafe_new("eta")
  assert_true(eta < @rewrite.RuleName::unsafe_new("beta"))
}
```

### `RuleNameError`, `RuleNameError::equal`

`RuleNameError` lists the reasons a rule name is invalid.

```mbti
pub(all) enum RuleNameError {
  Empty
} derive(Eq, @debug.Debug)
pub fn RuleNameError::equal(Self, Self) -> Bool
```

`Empty` is the only case: rule names must not be empty.

## Positions

### `ReductionFrame`, `ReductionFrame::equal`

`ReductionFrame` is one step from a node to one of its children.

```mbti
pub(all) enum ReductionFrame {
  BinderBody
  ApplyHead
  ApplyArgument(Int)
} derive(Eq, @debug.Debug)
pub fn ReductionFrame::equal(Self, Self) -> Bool
```

`BinderBody` enters the body of a `Bind`, `ApplyHead` the head of an
`Apply`, and `ApplyArgument(i)` its argument number `i`, counting from 0.

### `ReductionPath`

`ReductionPath` is the sequence of frames from the root to a position.

```mbti
pub struct ReductionPath {
  frames : Array[ReductionFrame]
} derive(Eq, @debug.Debug)
```

The empty path is the root.

### `ReductionPath::root`, `ReductionPath::prepend`, `ReductionPath::to_array`

These functions build and read paths.

```mbti
pub fn ReductionPath::root() -> Self
pub fn ReductionPath::prepend(Self, ReductionFrame) -> Self
pub fn ReductionPath::to_array(Self) -> Array[ReductionFrame]
```

`prepend(frame)` adds a frame at the root end, which is how a traversal
lifts the path of a step in a child to the parent. `to_array` returns the
frames root first.

### `ReductionPath::equal`

`ReductionPath::equal` compares two paths frame by frame.

```mbti
pub fn ReductionPath::equal(Self, Self) -> Bool
```

```moonbit
test "paths are built from the redex up" {
  let path = @rewrite.ReductionPath::root()
    .prepend(@rewrite.ApplyArgument(1))
    .prepend(@rewrite.BinderBody)
  assert_eq(path.to_array(), [@rewrite.BinderBody, @rewrite.ApplyArgument(1)])
  assert_eq(@rewrite.ReductionPath::root().to_array(), [])
}
```

## Single steps on `Term`

### `StepResult`, `StepResult::equal`

`StepResult[T]` is the outcome of one reduction attempt.

```mbti
pub(all) enum StepResult[T] {
  NoStep
  Reduced(before~ : @syntax.Term[T], after~ : @syntax.Term[T], rule~ : RuleName, path~ : ReductionPath)
} derive(Eq, @debug.Debug)
pub fn[T : Eq] StepResult::equal(Self[T], Self[T]) -> Bool
```

`NoStep` means the traversal found no position where the rule applies.
`Reduced` records the whole term `before`, the whole term `after`, the rule
and the path of the rewritten position. Exactly one position was rewritten:
the subterm of `before` at `path` is a redex of the rule, and `after` is
`before` with that subterm replaced by the rule's result. `equal` is the
promoted `Eq` implementation, which compares terms structurally.

### `top_down_once`

`top_down_once` rewrites the first position, in pre-order, at which the rule
applies.

```mbti
pub fn[T] top_down_once(@syntax.Term[T], RuleName, (@syntax.Term[T]) -> @syntax.Term[T]?) -> StepResult[T]
```

The rule is tried at a node before its children; children are visited head
first, then arguments from left to right, and binder bodies are entered. The
chosen position is the leftmost-outermost redex. `NoStep` means that the rule
applies nowhere in the term.

### `bottom_up_once`

`bottom_up_once` rewrites the first position, in post-order, at which the
rule applies.

```mbti
pub fn[T] bottom_up_once(@syntax.Term[T], RuleName, (@syntax.Term[T]) -> @syntax.Term[T]?) -> StepResult[T]
```

Children are tried before their parent, in the same left-to-right order. The
chosen position is the leftmost-innermost redex. `NoStep` again means that
the rule applies nowhere.

```moonbit
fn drop_zero(t : @syntax.Term[String]) -> @syntax.Term[String]? {
  match t {
    Apply(Value("+"), [Value("0"), other]) => Some(other)
    _ => None
  }
}

test "outermost versus innermost" {
  let rule = @rewrite.RuleName::unsafe_new("drop_zero")
  let inner : @syntax.Term[String] = Apply(Value("+"), [Value("0"), Value("1")])
  let outer : @syntax.Term[String] = Apply(Value("+"), [Value("0"), inner])
  match @rewrite.top_down_once(outer, rule, drop_zero) {
    Reduced(after~, path~, ..) => {
      assert_eq(after, inner)
      assert_eq(path.to_array(), [])
    }
    NoStep => fail("expected a step")
  }
  match @rewrite.bottom_up_once(outer, rule, drop_zero) {
    Reduced(after~, path~, ..) => {
      assert_eq(after, Apply(Value("+"), [Value("0"), Value("1")]))
      assert_eq(path.to_array(), [@rewrite.ApplyArgument(1)])
    }
    NoStep => fail("expected a step")
  }
}
```

## Repeating steps on `Term`

### `NormalizationResult`, `NormalizationResult::equal`

`NormalizationResult[T]` is the outcome of bounded repetition of a step
function.

```mbti
pub(all) enum NormalizationResult[T] {
  NormalForm(term~ : @syntax.Term[T], steps~ : Int)
  StepLimitReached(term~ : @syntax.Term[T], steps~ : Int)
} derive(Eq, @debug.Debug)
pub fn[T : Eq] NormalizationResult::equal(Self[T], Self[T]) -> Bool
```

`NormalForm(term, steps)`: the step function returns `NoStep` on `term`,
which was reached after `steps` steps. `StepLimitReached(term, steps)`: the
limit of `steps` steps was used up and `term` can still be reduced.

### `normalize`

`normalize` applies a step function until it returns `NoStep` or a step limit
is reached.

```mbti
pub fn[T] normalize(@syntax.Term[T], (@syntax.Term[T]) -> StepResult[T], Int) -> NormalizationResult[T]
```

`normalize(term, step, max_steps)` performs at most `max_steps` successful
steps and calls `step` at most `max_steps + 1` times: after the last allowed
step it calls `step` once more to decide between `NormalForm` and
`StepLimitReached`. With `max_steps <= 0` it performs no step and only
classifies `term`. The step function decides the strategy; see
[eval](eval.md) for ready-made ones.

### `ReductionTrace`, `ReductionTrace::initial`, `ReductionTrace::steps`, `ReductionTrace::result`, `ReductionTrace::equal`

`ReductionTrace[T]` records a bounded run: the initial term, every successful
step and the final result.

```mbti
pub struct ReductionTrace[T] {
  initial : @syntax.Term[T]
  steps : Array[StepResult[T]]
  result : NormalizationResult[T]
} derive(Eq, @debug.Debug)
pub fn[T] ReductionTrace::initial(Self[T]) -> @syntax.Term[T]
pub fn[T] ReductionTrace::steps(Self[T]) -> Array[StepResult[T]]
pub fn[T] ReductionTrace::result(Self[T]) -> NormalizationResult[T]
pub fn[T : Eq] ReductionTrace::equal(Self[T], Self[T]) -> Bool
```

`initial()`, `steps()` and `result()` read the three fields; `steps()`
returns a copy, and `equal` is the promoted `Eq` implementation. Every
element of `steps` is a `Reduced` value, and `steps().length()` equals the
`steps` count of `result`. When the step function keeps the contract of
`StepResult` (it reports its own input as `before`, as every traversal of
this package and of [eval](eval.md) does), consecutive steps chain: the first
`before` is `initial`, and the `after` of one step is the `before` of the
next. `trace` stores whatever the step function returns, so a hand-written
step that reports another `before` breaks the chain.

### `trace`

`trace` runs the same loop as `normalize` and records every step.

```mbti
pub fn[T] trace(@syntax.Term[T], (@syntax.Term[T]) -> StepResult[T], Int) -> ReductionTrace[T]
```

```moonbit
fn decrement(t : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  match t {
    Value(n) if n > 0 => Some(Value(n - 1))
    _ => None
  }
}

test "normalize and trace" {
  let rule = @rewrite.RuleName::unsafe_new("decrement")
  let step = (t : @syntax.Term[Int]) => @rewrite.top_down_once(t, rule, decrement)
  assert_eq(
    @rewrite.normalize(Value(3), step, 10),
    NormalForm(term=Value(0), steps=3),
  )
  let run = @rewrite.trace(Value(3), step, 2)
  assert_eq(run.steps().length(), 2)
  assert_eq(run.result(), StepLimitReached(term=Value(1), steps=2))
  assert_eq(run.initial(), Value(3))
}
```

## Binding-aware ASTs

### `GenericStepResult`, `GenericStepResult::equal`

`GenericStepResult[N]` is `StepResult` for a downstream AST `N`.

```mbti
pub(all) enum GenericStepResult[N] {
  NoStep
  Reduced(before~ : N, after~ : N, rule~ : RuleName, path~ : ReductionPath)
} derive(Eq, @debug.Debug)
pub fn[N : Eq] GenericStepResult::equal(Self[N], Self[N]) -> Bool
```

### `generic_top_down_once`

`generic_top_down_once` is `top_down_once` for any `BindingSyntax` AST.

```mbti
pub fn[N : @syntax.BindingSyntax] generic_top_down_once(N, RuleName, (N) -> N?) -> GenericStepResult[N]
```

The traversal uses `BindingSyntax::project` to find children and the trait
constructors to rebuild the parents of the rewritten node. `Opaque` and
variable nodes have no children; the rule is still tried on them.

### `GenericNormalizationResult`, `GenericNormalizationResult::equal`

`GenericNormalizationResult[N]` is `NormalizationResult` for a downstream
AST.

```mbti
pub(all) enum GenericNormalizationResult[N] {
  NormalForm(term~ : N, steps~ : Int)
  StepLimitReached(term~ : N, steps~ : Int)
} derive(Eq, @debug.Debug)
pub fn[N : Eq] GenericNormalizationResult::equal(Self[N], Self[N]) -> Bool
```

### `generic_normalize`

`generic_normalize` repeats `generic_top_down_once` with one rule until no
step applies or the step limit is reached.

```mbti
pub fn[N : @syntax.BindingSyntax] generic_normalize(N, RuleName, (N) -> N?, Int) -> GenericNormalizationResult[N]
```

It has the same step-count contract as `normalize`, with the top-down
strategy fixed.

```moonbit
test "generic rewriting on Term" {
  let rule = @rewrite.RuleName::unsafe_new("drop_zero")
  let inner : @syntax.Term[String] = Apply(Value("+"), [Value("0"), Value("1")])
  let outer : @syntax.Term[String] = Apply(Value("+"), [Value("0"), inner])
  assert_eq(
    @rewrite.generic_normalize(outer, rule, drop_zero, 10),
    NormalForm(term=Value("1"), steps=2),
  )
}
```

For a downstream AST see the [adapter tutorial](../tutorial/adapter.md).
