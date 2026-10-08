# substitution tutorial

This tutorial replaces variables by terms: instantiating a template, swapping
variables, substituting under binders without capturing anything, composing
substitutions and evaluating partially. The examples encode arithmetic as
`Term[String]`, with operators as values: $x + 1$ is
`Apply(Value("+"), [Variable(x), Value("1")])`.

| I want to | Use |
| --- | --- |
| replace one variable by a term | `Substitution::singleton(x, t).apply(term)` |
| replace several variables at once | `Substitution::set`, `apply` |
| substitute one substitution after another in one pass | `Substitution::then` |
| keep only the entries that matter | `restrict`, `without` |
| substitute in my own AST | `GenericSubstitution::apply_once` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
}
```

Substitute $2$ for $x$ in $x + 1$:

```moonbit
test "quick start: x + 1 with x := 2" {
  let x = @core.Name::new("x")
  let term : @syntax.Term[String] = Apply(Value("+"), [Variable(x), Value("1")])
  let s = @substitution.Substitution::singleton(x, @syntax.Value("2"))
  assert_eq(s.apply(term), Apply(Value("+"), [Value("2"), Value("1")]))
}
```

## Everyday tasks

The examples below share two helpers:

```moonbit
fn name(text : String) -> @core.Name {
  @core.Name::new(text)
}

fn plus(a : @syntax.Term[String], b : @syntax.Term[String]) -> @syntax.Term[String] {
  @syntax.Apply(@syntax.Value("+"), [a, b])
}
```

### Swap two variables

All entries of a substitution apply at the same time, so a swap needs no
temporary variable:

```moonbit
test "swap x and y" {
  let x = name("x")
  let y = name("y")
  let swap = @substitution.Substitution::singleton(x, @syntax.Term::Variable(y))
    .set(y, @syntax.Term::Variable(x))
  assert_eq(swap.apply(plus(Variable(x), Variable(y))), plus(Variable(y), Variable(x)))
}
```

### Substitute under a binder

Substituting $y$ for $x$ in $\lambda y.\, x + y$ must not turn the inserted
$y$ into the bound one. The binder is renamed to `y_1`:

```moonbit
test "no capture under a binder" {
  let x = name("x")
  let y = name("y")
  let term : @syntax.Term[String] = Bind(y, plus(Variable(x), Variable(y)))
  let result = @substitution.Substitution::singleton(x, @syntax.Term::Variable(y))
    .apply(term)
  let y1 = name("y_1")
  let expected : @syntax.Term[String] = Bind(y1, plus(Variable(y), Variable(y1)))
  assert_eq(result, expected)
}
```

A binder for the substituted variable itself shadows it, so nothing happens
inside:

```moonbit
test "a binder shadows the substituted variable" {
  let x = name("x")
  let term : @syntax.Term[String] = Bind(x, Variable(x))
  let s = @substitution.Substitution::singleton(x, @syntax.Value("0"))
  assert_eq(s.apply(term), term)
}
```

### Evaluate partially

Substitute the variables you know and leave the others in place:

```moonbit
test "partial evaluation" {
  let x = name("x")
  let y = name("y")
  let known = @substitution.Substitution::singleton(x, @syntax.Value("3"))
  let result = known.apply(plus(Variable(x), Variable(y)))
  assert_eq(result, plus(Value("3"), Variable(y)))
  assert_true(@syntax.free_variables(result).contains(y))
}
```

### Compose substitutions

`first.then(second)` is one substitution that does `first` and then
`second`. It is applied in a single traversal:

```moonbit
test "compose two steps into one" {
  let x = name("x")
  let y = name("y")
  let first = @substitution.Substitution::singleton(x, plus(Variable(y), Value("1")))
  let second = @substitution.Substitution::singleton(y, @syntax.Value("5"))
  let both = first.then(second)
  let term = plus(Variable(x), Variable(y))
  assert_eq(both.apply(term), plus(plus(Value("5"), Value("1")), Value("5")))
  assert_true(@syntax.alpha_equal(both.apply(term), second.apply(first.apply(term))))
}
```

## Going further

### Implement beta reduction

Beta reduction $(\lambda x.\,b)\,a \to b[x := a]$ is one substitution. This
is how [`@lambda.beta_rule`](../api/utlc/lambda.md) works:

```moonbit
fn beta(t : @syntax.Term[String]) -> @syntax.Term[String]? {
  match t {
    Apply(Bind(x, body), [arg]) =>
      Some(@substitution.Substitution::singleton(x, arg).apply(body))
    _ => None
  }
}

test "beta via substitution" {
  let x = name("x")
  let y = name("y")
  let k : @syntax.Term[String] = Bind(x, Bind(y, Variable(x)))
  let result = beta(Apply(k, [Variable(y)]))
  let expected : @syntax.Term[String] = Bind(name("y_1"), Variable(y))
  assert_eq(result, Some(expected))
}
```

### Iterate to a fixed point yourself

A substitution is applied once. If replacements may mention variables of the
domain and you want those replaced too, apply repeatedly, with a bound,
because the process need not terminate (think of $x := x + 1$):

```moonbit
fn apply_until_stable(
  s : @substitution.Substitution[String],
  t : @syntax.Term[String],
  limit : Int,
) -> @syntax.Term[String] {
  let mut current = t
  for _ in 0..<limit {
    let next = s.apply(current)
    if next == current {
      break
    }
    current = next
  }
  current
}

test "resolve a chain of definitions" {
  let x = name("x")
  let y = name("y")
  let defs = @substitution.Substitution::singleton(x, @syntax.Term::Variable(y))
    .set(y, @syntax.Value("7"))
  assert_eq(apply_until_stable(defs, Variable(x), 10), Value("7"))
}
```

### Substitute in your own AST

`GenericSubstitution` runs the same algorithm on any AST that implements
`@syntax.BindingSyntax`. The [adapter tutorial](adapter.md) defines such an
AST and substitutes in it with `apply_once`.

## Common pitfalls

- **Ambiguous constructors.** `@syntax.Variable(y)` is ambiguous when no type
  is expected, because `BindingView` also has a `Variable` case. Write
  `@syntax.Term::Variable(y)`, or annotate the expected type.
- **Expecting repeated substitution.** $\{x \mapsto y,\ y \mapsto 7\}$
  applied to $x$ gives $y$, not $7$. Use `then` or iterate explicitly.
- **Comparing with `==`.** Results may contain renamed binders (`y_1`).
  Compare with `@syntax.alpha_equal` unless you know the exact names.
- **Variables inside values.** `Value` payloads are not substituted into.

## Next steps

- [substitution API](../api/substitution.md) for every function.
- [substitution design](../design/substitution.md) for the definition and the
  composition and substitution lemmas.
- [rewrite tutorial](rewrite.md) to apply rules, built from substitution,
  anywhere in a term.
