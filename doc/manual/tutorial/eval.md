# eval tutorial

This tutorial runs a rewrite rule with the named strategies of `eval`:
normal order, applicative order and weak head. You will see where they agree,
where they differ, and how to write a strategy of your own. The examples use
the beta rule of the untyped lambda calculus from `utlc/lambda`.

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```text
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/eval",
  "Luna-Flow/type_theory/utlc/lambda",
}
```

Apply the identity function to `42`:

```moonbit
test "quick start: (λx. x) 42" {
  let x = @core.Name::new("x")
  let term : @syntax.Term[Int] = Apply(Bind(x, Variable(x)), [Value(42)])
  let beta = @rewrite.RuleName::unsafe_new("beta")
  assert_eq(
    @eval.evaluate(term, beta, @lambda.beta_rule, NormalOrder, 10),
    NormalForm(term=Value(42), steps=1),
  )
}
```

## Everyday tasks

The tasks share these helpers:

```moonbit
fn nm(text : String) -> @core.Name {
  @core.Name::new(text)
}

fn omega() -> @syntax.Term[Int] {
  let w = nm("w")
  let self_apply : @syntax.Term[Int] = Bind(w, Apply(Variable(w), [Variable(w)]))
  Apply(self_apply, [self_apply])
}

fn beta_name() -> @rewrite.RuleName {
  @rewrite.RuleName::unsafe_new("beta")
}
```

### Pick a strategy that terminates

Normal order is normalizing: if a term has a normal form, it finds it.
Applicative order evaluates arguments first and loops on a divergent
argument even when it is thrown away:

```moonbit
test "discarding a divergent argument" {
  let term : @syntax.Term[Int] = Apply(Bind(nm("x"), Value(0)), [omega()])
  assert_eq(
    @eval.evaluate(term, beta_name(), @lambda.beta_rule, NormalOrder, 20),
    NormalForm(term=Value(0), steps=1),
  )
  match @eval.evaluate(term, beta_name(), @lambda.beta_rule, ApplicativeOrder, 20) {
    StepLimitReached(steps~, ..) => assert_eq(steps, 20)
    NormalForm(..) => fail("applicative order should loop on omega")
  }
}
```

### Evaluate only to weak head normal form

`WeakHead` stops as soon as the term is an abstraction or an application with
a non-reducible head. It does not look inside:

```moonbit
test "weak head normal form" {
  let x = nm("x")
  let f = nm("f")
  let id : @syntax.Term[Int] = Bind(x, Variable(x))
  let term : @syntax.Term[Int] = Apply(id, [Bind(f, Apply(id, [Variable(f)]))])
  match @eval.evaluate(term, beta_name(), @lambda.beta_rule, WeakHead, 10) {
    NormalForm(term=result, steps~) => {
      assert_eq(steps, 1)
      assert_true(result is Bind(_, Apply(_, _)))
    }
    StepLimitReached(..) => fail("one step suffices")
  }
}
```

The result $\lambda f.\,(\lambda x.\,x)\,f$ still contains a redex under the
binder; `NormalOrder` would reduce it.

### Trace the steps

`trace` records each step with its path, which is useful to explain a
normalization or to compare two strategies step by step:

```moonbit
test "trace normal order" {
  let x = nm("x")
  let y = nm("y")
  let k : @syntax.Term[Int] = Bind(x, Bind(y, Variable(x)))
  let term : @syntax.Term[Int] = Apply(k, [Value(1), omega()])
  let run = @eval.trace(term, beta_name(), @lambda.beta_rule, NormalOrder, 10)
  let paths = run
    .steps()
    .map(s => match s {
      Reduced(path~, ..) => path.to_array().length()
      NoStep => -1
    })
  assert_eq(paths, [0, 0])
  assert_eq(run.result(), NormalForm(term=Value(1), steps=2))
}
```

Both steps happen at the root: first $K\,1$ is contracted inside the spine
$K\,1\,\Omega$, then the result is applied to $\Omega$, which is discarded.

### Use a domain rule

Strategies work with any rule, not only beta. Here a rule folds additions of
literals; normal order folds the outer addition last:

```moonbit
fn fold_add(t : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  match t {
    Apply(Variable(op), [Value(a), Value(b)]) if op.text() == "add" => Some(Value(a + b))
    _ => None
  }
}

test "fold additions" {
  let add = @syntax.Term::Variable(nm("add"))
  let term : @syntax.Term[Int] = Apply(add, [Apply(add, [Value(1), Value(2)]), Value(3)])
  let rule = @rewrite.RuleName::unsafe_new("fold_add")
  assert_eq(
    @eval.evaluate(term, rule, fold_add, NormalOrder, 10),
    NormalForm(term=Value(6), steps=2),
  )
}
```

## Going further

### Write your own strategy

Any function from a term to a `StepResult` is a strategy for
`@rewrite.normalize`. This one reduces only at the root, which is useful to
test a rule in isolation:

```moonbit
fn root_only(
  rule : (@syntax.Term[Int]) -> @syntax.Term[Int]?,
) -> (@syntax.Term[Int]) -> @rewrite.StepResult[Int] {
  t => match rule(t) {
    Some(after) =>
      Reduced(before=t, after~, rule=beta_name(), path=@rewrite.ReductionPath::root())
    None => NoStep
  }
}

test "a root-only strategy" {
  let x = nm("x")
  let term : @syntax.Term[Int] = Bind(x, Apply(Bind(x, Variable(x)), [Value(5)]))
  assert_eq(
    @rewrite.normalize(term, root_only(@lambda.beta_rule), 10),
    NormalForm(term~, steps=0),
  )
}
```

A hand-written step must keep the contract of `StepResult`: `after` is
`before` with exactly the subterm at `path` rewritten.

### Check strategies against each other

For a confluent rule such as beta, two strategies that both reach a normal
form agree up to alpha-equivalence. This makes a cheap regression test:

```moonbit
test "strategies agree when both terminate" {
  let x = nm("x")
  let y = nm("y")
  let term : @syntax.Term[Int] = Apply(Bind(x, Apply(Variable(x), [Variable(x)])), [
    Bind(y, Variable(y)),
  ])
  match
    (
      @eval.evaluate(term, beta_name(), @lambda.beta_rule, NormalOrder, 20),
      @eval.evaluate(term, beta_name(), @lambda.beta_rule, ApplicativeOrder, 20),
    ) {
    (NormalForm(term=a, ..), NormalForm(term=b, ..)) =>
      assert_true(@syntax.alpha_equal(a, b))
    _ => fail("both strategies terminate here")
  }
}
```

## Common pitfalls

- **Reading `WeakHead`'s `NormalForm` as a full normal form.** It only means
  weak head normal form.
- **Expecting `FullNormal` to differ from `NormalOrder`.** Today they use the
  same traversal.
- **Comparing results with `==`.** Beta reduction renames binders (`y_1`);
  compare with `@syntax.alpha_equal`.
- **Too small a step limit.** `StepLimitReached` does not mean divergence.
  Raise the limit, or use [utlc/nbe](utlc/nbe.md) for fast untyped
  normalization.

## Next steps

- [eval API](../api/eval.md) for the exact signatures.
- [eval design](../design/eval.md) for the definitions of the strategies and
  the classical theorems behind them.
- [utlc/lambda tutorial](utlc/lambda.md) for the lambda calculus built on
  these strategies.
