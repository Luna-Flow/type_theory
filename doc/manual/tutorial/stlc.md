# stlc tutorial

This tutorial type-checks simply typed lambda terms, explains type errors,
normalizes well-typed terms, and decides whether two terms are equal up to
beta and eta. Terms are the shared `@syntax.Term[@stlc.Atom]`, so everything
you know from [syntax](syntax.md) applies.

| I want to | Use |
| --- | --- |
| declare typed constants and variables | `Signature`, `TypeContext`, `extend_with` |
| find the type of a term | `infer` |
| check a function against its type | `check` |
| get the canonical normal form | `normalize_eta_long` |
| decide whether two terms are beta-eta equal | compare their eta-long forms with `@syntax.alpha_equal` |
| normalize step by step with a count | `normalize_checked` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/stlc",
}
```

Check the identity function against $A \to A$:

```moonbit
test "quick start: λx. x : A → A" {
  let x = @core.Name::new("x")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let id : @stlc.Term = Bind(x, Variable(x))
  let result = @stlc.check(
    @stlc.Signature::empty(),
    @stlc.TypeContext::empty(),
    id,
    @stlc.Ty::Arrow(a, a),
  )
  assert_eq(result, Ok(()))
}
```

## Everyday tasks

These helpers keep the examples short:

```moonbit
fn sn(s : String) -> @core.Name {
  @core.Name::new(s)
}

fn base(s : String) -> @stlc.Ty {
  @stlc.Ty::Base(sn(s))
}

fn arrow(a : @stlc.Ty, b : @stlc.Ty) -> @stlc.Ty {
  @stlc.Ty::Arrow(a, b)
}

fn tv(s : String) -> @stlc.Term {
  @syntax.Term::Variable(sn(s))
}

fn tc(s : String) -> @stlc.Term {
  @syntax.Term::Value(@stlc.Atom::Const(sn(s)))
}

fn tlam(s : String, body : @stlc.Term) -> @stlc.Term {
  @syntax.Term::Bind(sn(s), body)
}

fn tapp(f : @stlc.Term, args : Array[@stlc.Term]) -> @stlc.Term {
  @syntax.Term::Apply(f, args)
}
```

### Declare constants and variables

A `Signature` types the constants of your language, a `TypeContext` the free
variables of the term being checked. Applications are then inferred:

```moonbit
test "infer the type of an application" {
  let nat = base("Nat")
  let sig = @stlc.Signature::empty()
    .extend_with(sn("zero"), nat)
    .extend_with(sn("succ"), arrow(nat, nat))
  let ctx = @stlc.TypeContext::empty().extend_with(sn("n"), nat)
  let term = tapp(tc("succ"), [tapp(tc("succ"), [tv("n")])])
  assert_eq(@stlc.infer(sig, ctx, term), Ok(nat))
}
```

### Explain a type error

Every rejection is a `TypeError` value you can match on and report:

```moonbit
fn explain(e : @stlc.TypeError) -> String {
  match e {
    UnboundVariable(x) => "unbound variable \{x.text()}"
    UnknownConstant(c) => "unknown constant \{c.text()}"
    CannotInferLambda => "a lambda needs an expected type"
    ExpectedFunction(_) => "applying a non-function"
    TypeMismatch(..) => "type mismatch"
    EmptyApplication => "application without arguments"
    ScopeError(_) | NormalizationError(..) => "internal error"
  }
}

test "report errors" {
  let sig = @stlc.Signature::empty().extend_with(sn("zero"), base("Nat"))
  let ctx = @stlc.TypeContext::empty()
  let errors = [
    @stlc.infer(sig, ctx, tv("y")),
    @stlc.infer(sig, ctx, tlam("x", tv("x"))),
    @stlc.infer(sig, ctx, tapp(tc("zero"), [tc("zero")])),
  ].map(r => match r {
    Ok(_) => "ok"
    Err(e) => explain(e)
  })
  inspect(
    errors.join("; "),
    content="unbound variable y; a lambda needs an expected type; applying a non-function",
  )
}
```

### Check functions against their types

Lambdas are checked, not inferred: give the expected type and the checker
pushes it into the body.

```moonbit
test "check a higher-order function" {
  let a = base("A")
  let b = base("B")
  // twice = λf. λx. f (f x) : (A → A) → A → A
  let twice = tlam("f", tlam("x", tapp(tv("f"), [tapp(tv("f"), [tv("x")])])))
  let empty_sig = @stlc.Signature::empty()
  let empty_ctx = @stlc.TypeContext::empty()
  assert_eq(@stlc.check(empty_sig, empty_ctx, twice, arrow(arrow(a, a), arrow(a, a))), Ok(()))
  assert_true(
    @stlc.check(empty_sig, empty_ctx, twice, arrow(arrow(a, b), arrow(a, b))) is Err(TypeMismatch(..)),
  )
}
```

A redex is checked in the same way when it returns a lambda: the checker
infers the type of the argument, gives it to the parameter, and checks the
returned lambda against the expected type.

```moonbit
test "check a redex that returns a lambda" {
  let a = base("A")
  let empty_sig = @stlc.Signature::empty()
  let empty_ctx = @stlc.TypeContext::empty()
  // (λk. λx. x) k : A → A, with k : A in the context
  let ctx = empty_ctx.extend_with(sn("k"), a)
  let redex = tapp(tlam("k", tlam("x", tv("x"))), [tv("k")])
  assert_eq(@stlc.check(empty_sig, ctx, redex, arrow(a, a)), Ok(()))
  // the argument given to the lambda must be inferable
  let lambda_argument = tapp(tlam("k", tlam("x", tv("x"))), [tlam("z", tv("z"))])
  assert_true(
    @stlc.check(empty_sig, empty_ctx, lambda_argument, arrow(a, a)) is Err(CannotInferLambda),
  )
}
```

### Normalize a well-typed term

`normalize_eta_long` returns the canonical form: beta-normal, and every
function-typed subterm written as a lambda.

```moonbit
test "normalize to eta-long form" {
  let a = base("A")
  let sig = @stlc.Signature::empty().extend_with(sn("g"), arrow(a, arrow(a, a)))
  let ctx = @stlc.TypeContext::empty()
  // (λh. h) g  normalizes to  λx. λx_1. g x x_1
  let term = tapp(tlam("h", tv("h")), [tc("g")])
  let expected = tlam("p", tlam("q", tapp(tapp(tc("g"), [tv("p")]), [tv("q")])))
  match @stlc.normalize_eta_long(sig, ctx, term, arrow(a, arrow(a, a))) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => fail("well typed")
  }
}
```

The redex $(\lambda h.\,h)\,g$ is inferred by giving `h` the type of `g`.

### Decide beta-eta equality

Two well-typed terms of the same type are $\beta\eta$-equal exactly when their
eta-long normal forms are alpha-equivalent:

```moonbit
fn beta_eta_equal(
  sig : @stlc.Signature,
  ctx : @stlc.TypeContext,
  ty : @stlc.Ty,
  s : @stlc.Term,
  t : @stlc.Term,
) -> Bool {
  match (@stlc.normalize_eta_long(sig, ctx, s, ty), @stlc.normalize_eta_long(sig, ctx, t, ty)) {
    (Ok(ns), Ok(nt)) => @syntax.alpha_equal(ns, nt)
    _ => false
  }
}

test "eta and beta equalities" {
  let a = base("A")
  let ctx = @stlc.TypeContext::empty().extend_with(sn("f"), arrow(a, a))
  let sig = @stlc.Signature::empty()
  let wrapped = tlam("x", tapp(tv("f"), [tv("x")]))
  assert_true(beta_eta_equal(sig, ctx, arrow(a, a), tv("f"), wrapped))
  let composed = tlam("x", tapp(tlam("y", tapp(tv("f"), [tv("y")])), [tv("x")]))
  assert_true(beta_eta_equal(sig, ctx, arrow(a, a), composed, tv("f")))
  let twice = tlam("x", tapp(tv("f"), [tapp(tv("f"), [tv("x")])]))
  assert_false(beta_eta_equal(sig, ctx, arrow(a, a), twice, tv("f")))
}
```

## Going further

### Operational normalization with a trace

`normalize_checked` type-checks and then runs the untyped normal-order
beta-eta reducer, which gives eta-*short* results and step counts. Use it when
you want the reference semantics:

```moonbit
test "operational normalization" {
  let u = @stlc.Ty::Unit
  let unit_value = @syntax.Term::Value(@stlc.Atom::UnitLit)
  let k = tlam("x", tlam("y", tv("x")))
  let term = tapp(k, [unit_value, unit_value])
  assert_eq(
    @stlc.normalize_checked(@stlc.Signature::empty(), @stlc.TypeContext::empty(), term, u, 10),
    Ok(NormalForm(term=unit_value, steps=2)),
  )
}
```

For a full trace, check the term and call `@eval.trace` with
`@lambda.beta_eta_rule` yourself.

### Use the substrate on typed terms

Because `@stlc.Term` is `@syntax.Term[@stlc.Atom]`, substitution, free
variables and rewriting work unchanged. Substituting a well-typed term of the
right type for a variable preserves typing (the substitution lemma of typed
calculi), so you can instantiate a typed template with
`@substitution.Substitution` and re-check it.

## Common pitfalls

- **Inferring a lambda.** `infer` on a lambda fails with `CannotInferLambda`.
  Use `check` with the expected type.
- **Unit eta.** A neutral term of type `Unit`, such as a variable `u : Unit`,
  is not replaced by `()`. `f u` and `f ()` have different normal forms.
- **Empty applications.** `Apply(f, [])` is rejected with
  `EmptyApplication`, also inside a spine such as `Apply(Apply(f, []), [a])`.
  Build applications with at least one argument.
- **Comparing normal forms with `==`.** Generated binders are `x`, `x_1`, …;
  compare with `@syntax.alpha_equal`.

## Next steps

- [stlc API](../api/stlc.md) for all types, errors and functions.
- [stlc design](../design/stlc.md) for the typing rules, the eta-long normal
  forms and the correctness argument of typed NbE.
- [utlc/nbe tutorial](utlc/nbe.md) for the untyped, fuel-bounded counterpart.
