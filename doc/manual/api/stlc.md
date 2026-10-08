# stlc API

## Purpose

The `stlc` package is the simply typed lambda calculus over the shared named
syntax: types, signatures of typed constants, typing contexts, bidirectional
type inference and checking, step-bounded operational normalization, and
typed normalization by evaluation to beta-normal, eta-long form.

Terms are `@syntax.Term[Atom]`: `Bind(x, b)` is $\lambda x.\,b$ (without a
type annotation), `Apply` is application, `Variable` a variable, and `Value`
holds an `Atom`. The typing rules and the NbE algorithm are given in the
[stlc design](../design/stlc.md).

## Importing

Add the package, and the packages whose types appear in its signatures, to
your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/stlc",
}
```

The examples on this page refer to every name through its package alias,
for example `@core.Name`.

## Syntax

### `Atom`, `Atom::equal`

`Atom` is a constant of the calculus.

```mbti
pub(all) enum Atom {
  UnitLit
  Const(@core.Name)
} derive(Eq, @debug.Debug)
pub fn Atom::equal(Self, Self) -> Bool
```

`UnitLit` is the unit value $()$; `Const(c)` is a constant whose type is
declared in a `Signature`.

### `Term`

`Term` is the type of STLC terms.

```mbti
pub type Term = @syntax.Term[Atom]
```

It is an alias, so all of [syntax](syntax.md), [substitution](substitution.md)
and [rewrite](rewrite.md) apply to STLC terms.

### `Ty`, `Ty::equal`

`Ty` is a simple type.

```mbti
pub(all) enum Ty {
  Base(@core.Name)
  Unit
  Arrow(Ty, Ty)
} derive(Eq, @debug.Debug)
pub fn Ty::equal(Self, Self) -> Bool
```

`Base(b)` is an uninterpreted base type, `Unit` the unit type, and
`Arrow(a, b)` the function type $a \to b$. Types are compared structurally
(`Ty::equal`, the promoted `Eq` implementation); for simple types this is
exactly type equality. `Atom::equal` likewise compares constants by name.

## Signatures and contexts

### `Signature`, `Signature::empty`, `Signature::extend_with`, `Signature::lookup`, `Signature::to_array`, `Signature::equal`

`Signature` assigns types to constants.

```mbti
pub struct Signature {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, @debug.Debug)
pub fn Signature::empty() -> Self
#alias(extend, deprecated)
pub fn Signature::extend_with(Self, @core.Name, Ty) -> Self
pub fn Signature::lookup(Self, @core.Name) -> Ty?
pub fn Signature::to_array(Self) -> Array[(@core.Name, Ty)]
pub fn Signature::equal(Self, Self) -> Bool
```

`empty()` has no constants. `extend_with(c, ty)` returns a new signature
with `c : ty` added; a later entry for the same name shadows an earlier one,
and `lookup` returns the latest, or `None`. `to_array` returns a copy of the
entries in insertion order, and `equal` compares the entry lists.

### `TypeContext`, `TypeContext::empty`, `TypeContext::extend_with`, `TypeContext::lookup`, `TypeContext::to_array`, `TypeContext::equal`

`TypeContext` assigns types to free variables.

```mbti
pub struct TypeContext {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, @debug.Debug)
pub fn TypeContext::empty() -> Self
#alias(extend, deprecated)
pub fn TypeContext::extend_with(Self, @core.Name, Ty) -> Self
pub fn TypeContext::lookup(Self, @core.Name) -> Ty?
pub fn TypeContext::to_array(Self) -> Array[(@core.Name, Ty)]
pub fn TypeContext::equal(Self, Self) -> Bool
```

The functions behave as those of `Signature`, with the same shadowing rule:
the type checker extends the context when it enters a lambda, so the nearest
binder of a name wins.

```moonbit
test "signatures and contexts" {
  let c = @core.Name::new("c")
  let x = @core.Name::new("x")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let sig = @stlc.Signature::empty().extend_with(c, @stlc.Ty::Arrow(a, a))
  let ctx = @stlc.TypeContext::empty().extend_with(x, a).extend_with(x, @stlc.Ty::Unit)
  assert_eq(sig.lookup(c), Some(@stlc.Ty::Arrow(a, a)))
  assert_eq(ctx.lookup(x), Some(@stlc.Ty::Unit))
  assert_eq(ctx.to_array().length(), 2)
}
```

## Errors

### `TypeError`, `TypeError::equal`

`TypeError` reports why a term is rejected.

```mbti
pub(all) enum TypeError {
  UnboundVariable(@core.Name)
  UnknownConstant(@core.Name)
  CannotInferLambda
  ExpectedFunction(Ty)
  TypeMismatch(expected~ : Ty, actual~ : Ty)
  EmptyApplication
  ScopeError(@debruijn.ScopeError)
  NormalizationError(message~ : String)
} derive(Eq, @debug.Debug)
pub fn TypeError::equal(Self, Self) -> Bool
```

| Case | Meaning |
| --- | --- |
| `UnboundVariable(x)` | `x` is not in the context. |
| `UnknownConstant(c)` | `c` is not in the signature. |
| `CannotInferLambda` | a lambda appears where its type must be inferred. |
| `ExpectedFunction(ty)` | a term of the non-function type `ty` is applied. |
| `TypeMismatch(expected, actual)` | the inferred type differs from the expected one. |
| `EmptyApplication` | `Apply(head, [])` has no argument. |
| `ScopeError(e)` | reserved for De Bruijn scope failures; not produced by the current functions. |
| `NormalizationError(message)` | an internal invariant of typed NbE failed; not expected for checked input. |

## Type checking

### `infer`

`infer` synthesizes the type of a term.

```mbti
pub fn infer(Signature, TypeContext, @syntax.Term[Atom]) -> Result[Ty, TypeError]
```

The unit literal has type `Unit`, constants and variables have their declared
types, and an application `f a_1 … a_n` has the result type of `f` after
checking each argument against the corresponding domain. A lambda alone
cannot be inferred (`CannotInferLambda`). A lambda applied directly to
arguments is inferred by inferring the first argument's type and the body
under that assumption.

### `check`

`check` verifies a term against a type.

```mbti
pub fn check(Signature, TypeContext, @syntax.Term[Atom], Ty) -> Result[Unit, TypeError]
```

A lambda checks against an arrow type by checking its body against the
codomain, with the parameter given the domain. Every other term is inferred
and compared with `==`; a difference gives `TypeMismatch`.

```moonbit
test "infer and check" {
  let x = @core.Name::new("x")
  let f = @core.Name::new("f")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let id : @stlc.Term = Bind(x, Variable(x))
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty()
  assert_eq(@stlc.check(sig, ctx, id, @stlc.Ty::Arrow(a, a)), Ok(()))
  assert_eq(@stlc.infer(sig, ctx, id), Err(@stlc.TypeError::CannotInferLambda))
  let ctx_f = ctx.extend_with(f, @stlc.Ty::Arrow(a, a))
  let bad : @stlc.Term = Apply(Variable(f), [Value(@stlc.Atom::UnitLit)])
  assert_eq(
    @stlc.infer(sig, ctx_f, bad),
    Err(@stlc.TypeError::TypeMismatch(expected=a, actual=@stlc.Ty::Unit)),
  )
}
```

> [!WARNING]
> When a lambda is applied to two or more arguments, `infer` types the
> remaining arguments in a context that already contains the lambda's
> parameter. If one of those arguments mentions a free variable with the same
> name as the parameter, it is typed with the parameter's type, and the
> checker can then *accept a wrong type*. With `x : B` in the context,
> `check` accepts $(\lambda x.\,\lambda y.\,y)\;()\;x$ at `Unit` and rejects
> it at its real type `B`; `normalize_checked` then returns `x`, a term of
> type `B`, as a normal form "of type `Unit`". `normalize_eta_long` rejects
> the term at both types. Until this is fixed, make sure the parameter of
> such a redex does not occur free in the later arguments (rename it, or
> apply the arguments one at a time).

## Normalization

### `normalize_checked`

`normalize_checked` checks a term against a type and then normalizes it with
the untyped beta-eta reducer.

```mbti
pub fn normalize_checked(Signature, TypeContext, @syntax.Term[Atom], Ty, Int) -> Result[@rewrite.NormalizationResult[Atom], TypeError]
```

On a type error it returns `Err` without reducing. Otherwise it returns
`Ok(@lambda.normalize(term, max_steps))`: normal-order beta-eta reduction with
a step limit. Its normal forms are beta-normal and eta-*short* (for unary
applications, see [`@lambda.eta_rule`](utlc/lambda.md)). Because every
well-typed term is strongly normalizing, a large enough `max_steps` always
gives `NormalForm`. The result is only as trustworthy as `check`; see the
warning above.

### `normalize_eta_long`

`normalize_eta_long` checks a term against a type and returns its
beta-normal, eta-long form, computed by typed normalization by evaluation.

```mbti
pub fn normalize_eta_long(Signature, TypeContext, @syntax.Term[Atom], Ty) -> Result[@syntax.Term[Atom], TypeError]
```

In the result, every subterm of arrow type is a lambda, and every application
has a variable or a constant at its head. Variables of the context and
constants of the signature are kept as they are and eta-expanded according to
their types. No step limit is needed: well-typed terms always normalize. New
binder names are `x`, `x_1`, … chosen to avoid every name of the term and the
context.

```moonbit
test "beta-normal eta-long form" {
  let f = @core.Name::new("f")
  let x = @core.Name::new("x")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let ctx = @stlc.TypeContext::empty().extend_with(f, @stlc.Ty::Arrow(a, a))
  let sig = @stlc.Signature::empty()
  // f is eta-expanded to λx. f x
  let expected : @stlc.Term = Bind(x, Apply(Variable(f), [Variable(x)]))
  match @stlc.normalize_eta_long(sig, ctx, Variable(f), @stlc.Ty::Arrow(a, a)) {
    Ok(normal) => assert_true(@syntax.alpha_equal(normal, expected))
    Err(_) => fail("well typed")
  }
  // the operational normalizer contracts the redex but does not expand
  let redex : @stlc.Term = Apply(Bind(x, Variable(x)), [Variable(f)])
  assert_eq(
    @stlc.normalize_checked(sig, ctx, redex, @stlc.Ty::Arrow(a, a), 10),
    Ok(NormalForm(term=Variable(f), steps=1)),
  )
}
```

## Deprecated

| Deprecated | Replacement |
| --- | --- |
| `Signature::extend` | `Signature::extend_with` |
| `TypeContext::extend` | `TypeContext::extend_with` |

The hidden method forms `not_equal` and `to_repr` on the types of this package
are deprecated; use `!=` and `Repr(x)`.
