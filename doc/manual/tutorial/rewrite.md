# rewrite tutorial

This tutorial writes simplification rules for arithmetic terms, applies them
one step at a time, runs them to a normal form with a step limit, and reads
the trace to see which rule fired where. Terms are `Term[String]` with
operators as values: $x \cdot 1$ is
`Apply(Value("*"), [Variable(x), Value("1")])`.

| I want to | Use |
| --- | --- |
| apply a rule once, outermost first | `top_down_once` |
| apply a rule once, innermost first | `bottom_up_once` |
| repeat steps with a limit | `normalize` |
| keep every step for inspection | `trace` |
| name a rule | `RuleName::new` or, for literals, `RuleName::unsafe_new` |
| rewrite my own AST | `generic_top_down_once`, `generic_normalize` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.3.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
}
```

A rule is a function that rewrites a term at its root or returns `None`. The
rule $t \cdot 1 \to t$ simplifies $(x \cdot 1) \cdot 1$ in two steps:

```moonbit
fn times_one(t : @syntax.Term[String]) -> @syntax.Term[String]? {
  match t {
    Apply(Value("*"), [other, Value("1")]) => Some(other)
    _ => None
  }
}

test "quick start: x * 1 * 1" {
  let x = @syntax.Term::Variable(@core.Name::new("x"))
  let term : @syntax.Term[String] = Apply(Value("*"), [
    Apply(Value("*"), [x, Value("1")]),
    Value("1"),
  ])
  let rule = @rewrite.RuleName::unsafe_new("times_one")
  let step = (t : @syntax.Term[String]) => @rewrite.top_down_once(t, rule, times_one)
  assert_eq(@rewrite.normalize(term, step, 10), NormalForm(term=x, steps=2))
}
```

## Everyday tasks

These examples share a few helpers and a second rule, $0 + t \to t$:

```moonbit
fn op(name : String, a : @syntax.Term[String], b : @syntax.Term[String]) -> @syntax.Term[String] {
  @syntax.Apply(@syntax.Value(name), [a, b])
}

fn lit(text : String) -> @syntax.Term[String] {
  @syntax.Value(text)
}

fn var_(text : String) -> @syntax.Term[String] {
  @syntax.Term::Variable(@core.Name::new(text))
}

fn zero_plus(t : @syntax.Term[String]) -> @syntax.Term[String]? {
  match t {
    Apply(Value("+"), [Value("0"), other]) => Some(other)
    _ => None
  }
}
```

### Take one step and see where it happened

`top_down_once` rewrites the outermost-leftmost match and reports the path
to it:

```moonbit
test "one step with its position" {
  let term = op("*", lit("2"), op("+", lit("0"), var_("y")))
  let rule = @rewrite.RuleName::unsafe_new("zero_plus")
  match @rewrite.top_down_once(term, rule, zero_plus) {
    Reduced(after~, path~, rule=used, ..) => {
      assert_eq(after, op("*", lit("2"), var_("y")))
      assert_eq(path.to_array(), [@rewrite.ApplyArgument(1)])
      inspect(used.value(), content="zero_plus")
    }
    NoStep => fail("expected a step")
  }
}
```

`ApplyArgument(1)` is the second argument of the root `*`.

### Normalize with a step limit

A step limit protects against rules that never stop. Check which result you
got:

```moonbit
test "normal form or limit" {
  let term = op("+", lit("0"), op("+", lit("0"), var_("z")))
  let rule = @rewrite.RuleName::unsafe_new("zero_plus")
  let step = (t : @syntax.Term[String]) => @rewrite.top_down_once(t, rule, zero_plus)
  match @rewrite.normalize(term, step, 1) {
    StepLimitReached(term~, steps~) => {
      assert_eq(steps, 1)
      assert_eq(term, op("+", lit("0"), var_("z")))
    }
    NormalForm(..) => fail("one step is not enough")
  }
  assert_eq(@rewrite.normalize(term, step, 5), NormalForm(term=var_("z"), steps=2))
}
```

### Read a trace

`trace` keeps every step, so you can explain a simplification:

```moonbit
test "explain a simplification" {
  let term = op("+", lit("0"), op("+", lit("0"), var_("z")))
  let rule = @rewrite.RuleName::unsafe_new("zero_plus")
  let step = (t : @syntax.Term[String]) => @rewrite.top_down_once(t, rule, zero_plus)
  let run = @rewrite.trace(term, step, 10)
  let lines = run
    .steps()
    .map(s => match s {
      Reduced(rule~, path~, ..) => "\{rule.value()} at depth \{path.to_array().length()}"
      NoStep => "none"
    })
  inspect(lines.join("; "), content="zero_plus at depth 0; zero_plus at depth 0")
}
```

### Choose outermost or innermost

When redexes are nested, `top_down_once` takes the outer one and
`bottom_up_once` the inner one. With a confluent rule set both reach the same
normal form, but the steps differ:

```moonbit
test "outermost and innermost first steps" {
  let inner = op("+", lit("0"), var_("z"))
  let term = op("+", lit("0"), inner)
  let rule = @rewrite.RuleName::unsafe_new("zero_plus")
  match @rewrite.top_down_once(term, rule, zero_plus) {
    Reduced(path~, ..) => assert_eq(path.to_array().length(), 0)
    NoStep => fail("expected a step")
  }
  match @rewrite.bottom_up_once(term, rule, zero_plus) {
    Reduced(path~, ..) => assert_eq(path.to_array(), [@rewrite.ApplyArgument(1)])
    NoStep => fail("expected a step")
  }
}
```

### Combine several rules

Combine rules into one by trying them in order. The combined rule has one
name; give it a name that says so:

```moonbit
fn simplify(t : @syntax.Term[String]) -> @syntax.Term[String]? {
  match zero_plus(t) {
    Some(u) => Some(u)
    None => times_one(t)
  }
}

test "two rules, one normal form" {
  let term = op("+", lit("0"), op("*", var_("a"), lit("1")))
  let rule = @rewrite.RuleName::unsafe_new("simplify")
  let step = (t : @syntax.Term[String]) => @rewrite.top_down_once(t, rule, simplify)
  assert_eq(@rewrite.normalize(term, step, 10), NormalForm(term=var_("a"), steps=2))
}
```

If you need to know which of the rules fired, write a step function that
calls `top_down_once` once per rule, each with its own name, and returns the
first `Reduced`. That prefers the first rule anywhere in the term over the
second rule at an outer position.

## Going further

### Rules under binders

Traversals enter binder bodies, so a rule sees open terms. A rule that only
looks at the shape of a term, like the two above, is fine anywhere. A rule
that moves or duplicates subterms across binders must handle binding itself,
usually with [substitution](substitution.md). The beta rule of
[`@lambda`](utlc/lambda.md) is the standard example.

### Rewriting your own AST

`generic_top_down_once` and `generic_normalize` accept any AST that
implements `@syntax.BindingSyntax`. Write the rule against your own type; the
[adapter tutorial](adapter.md) shows a complete example.

### Strategies

[eval](eval.md) packages the traversals as named strategies (normal order,
applicative order, weak head) behind one `evaluate` function.

## Common pitfalls

- **A rule that does not make progress.** A rule that returns `Some(t)` for
  its own input $t$, or that undoes another rule, keeps the normalizer busy
  until the step limit. Check for `StepLimitReached`.
- **Non-confluent rules.** If two rules overlap without joining, different
  strategies can give different normal forms. Use the trace to find the
  overlap.
- **`unsafe_new` with input.** `RuleName::unsafe_new("")` aborts. Use
  `RuleName::new` for names that are not literals.
- **Ambiguous constructors.** `@syntax.Variable(x)` without an expected type
  is ambiguous; write `@syntax.Term::Variable(x)`.

## Next steps

- [rewrite API](../api/rewrite.md) for every type and function.
- [rewrite design](../design/rewrite.md) for rewriting theory, the one-redex
  contract and the normal-form lemma.
- [eval tutorial](eval.md) for named reduction strategies.
