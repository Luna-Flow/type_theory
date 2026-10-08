# utlc/lambda API

## Purpose

The `utlc/lambda` package is the untyped lambda calculus over the shared named
syntax `@syntax.Term[T]`: constructors for abstraction and application, the
beta and eta rules, and a bounded normal-order normalizer. It is the
reference operational semantics of the library.

In a lambda term, `Bind(x, b)` is $\lambda x.\,b$, `Apply(f, [a])` is
$f\,a$, and `Value(v)` is an opaque constant. The rules are explained in the
[utlc/lambda design](../../design/utlc/lambda.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/utlc/lambda",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

The default alias of the package is `@lambda`.

## Constructors

### `abstraction`

`abstraction` builds $\lambda x.\,body$.

```mbti
pub fn[T] abstraction(@core.Name, @syntax.Term[T]) -> @syntax.Term[T]
```

It returns `Bind(parameter, body)`.

### `application`

`application` builds the unary application $f\,a$.

```mbti
pub fn[T] application(@syntax.Term[T], @syntax.Term[T]) -> @syntax.Term[T]
```

It returns `Apply(function, [argument])`.

```moonbit
test "build (λx. x) y" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let id : @syntax.Term[Int] = @lambda.abstraction(x, Variable(x))
  let term = @lambda.application(id, Variable(y))
  assert_eq(term, Apply(Bind(x, Variable(x)), [Variable(y)]))
}
```

## Rules

### `beta_rule`

`beta_rule` contracts a beta redex at the root of a term.

```mbti
pub fn[T] beta_rule(@syntax.Term[T]) -> @syntax.Term[T]?
```

For `Apply(Bind(x, body), [a, ..rest])` it returns the capture-avoiding
substitution `body[x := a]`, applied to `rest` when `rest` is not empty. For
every other term it returns `None`; in particular an empty application
`Apply(Bind(x, body), [])` is not a redex, and neither is
`Apply(Apply(Bind(x, body), []), [a])`, whose head is not literally a `Bind`.
It works for any domain type `T`, because values are never inspected.

### `eta_rule`

`eta_rule` contracts an eta redex at the root of a term.

```mbti
pub fn[T] eta_rule(@syntax.Term[T]) -> @syntax.Term[T]?
```

For `Bind(x, Apply(f, [Variable(x)]))` with `x` not free in `f` it returns
`f`; otherwise `None`. Only a unary application is an eta redex:
`Bind(x, Apply(f, [a, Variable(x)]))` is not contracted.

### `beta_eta_rule`

`beta_eta_rule` tries `beta_rule` and, if it does not apply, `eta_rule`.

```mbti
pub fn[T] beta_eta_rule(@syntax.Term[T]) -> @syntax.Term[T]?
```

A term cannot be both a beta and an eta redex at the root (one is an
`Apply`, the other a `Bind`), so the order only documents priority.

```moonbit
test "beta and eta at the root" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let f = @core.Name::new("f")
  let k : @syntax.Term[Int] = Bind(x, Bind(y, Variable(x)))
  let expected : @syntax.Term[Int] = Bind(@core.Name::new("y_1"), Variable(y))
  assert_eq(@lambda.beta_rule(Apply(k, [Variable(y)])), Some(expected))
  let eta_redex : @syntax.Term[Int] = Bind(x, Apply(Variable(f), [Variable(x)]))
  assert_eq(@lambda.eta_rule(eta_redex), Some(Variable(f)))
  let not_eta : @syntax.Term[Int] = Bind(x, Apply(Variable(x), [Variable(x)]))
  assert_eq(@lambda.beta_eta_rule(not_eta), None)
}
```

## Normalization

### `normalize`

`normalize` reduces a term to beta-eta normal form with normal-order
reduction, within a step limit.

```mbti
pub fn[T] normalize(@syntax.Term[T], Int) -> @rewrite.NormalizationResult[T]
```

It is `@eval.evaluate(term, "beta_eta", beta_eta_rule, NormalOrder, max_steps)`:
at each step it contracts the leftmost-outermost beta or eta redex, anywhere
in the term, including under binders. `NormalForm(t, n)` means `t` has no
beta or eta redex (in the unary sense above) and was reached in `n` steps;
`StepLimitReached` means the limit was used up. Divergent terms such as
$\Omega$ always end with `StepLimitReached`.

```moonbit
test "normalize (λx. λy. x y) y" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let inner : @syntax.Term[Int] = Bind(y, Apply(Variable(x), [Variable(y)]))
  let term : @syntax.Term[Int] = Apply(Bind(x, inner), [Variable(y)])
  assert_eq(@lambda.normalize(term, 10), NormalForm(term=Variable(y), steps=2))
}
```

The first step is beta and produces $\lambda y_1.\,y\,y_1$; the second is eta.

Because `normalize` also contracts eta redexes, its result can differ from
the beta normal form that `@debruijn.normalize` and `@nbe.normalize` return:
$\lambda x.\,f\,x$ normalizes to $f$ here and stays $\lambda.\,f\,0$ there.
Use `@eval.evaluate` with `beta_rule` and `NormalOrder` when you need the
beta normal form.
