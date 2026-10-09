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

Every function of the package, `==` on types included, is stack-safe in the
nesting depth of terms and types: type checking, evaluation and readback run
as loops that keep pending work in heap arrays and use a constant amount of
host stack. Terms nested 100 000 levels deep (binders, argument positions,
curried spines, nested redexes) and types nested as deep (in codomains or in
domains) are handled on every backend. `Debug` of such a term, type or error
is not stack-safe.

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
} derive(@debug.Debug)
pub impl Eq for Ty
pub fn Ty::equal(Self, Self) -> Bool
```

`Base(b)` is an uninterpreted base type, `Unit` the unit type, and
`Arrow(a, b)` the function type $a \to b$. Types are compared structurally
(`Ty::equal`, the promoted `Eq` implementation); for simple types this is
exactly type equality. The implementation is written by hand rather than
derived so that it is stack-safe; it has the semantics of the derived one. `Atom::equal` likewise compares constants by name.

## Signatures and contexts

### `Signature`, `Signature::empty`, `Signature::extend_with`, `Signature::lookup`, `Signature::length`, `Signature::to_array`, `Signature::equal`

`Signature` assigns types to constants.

```mbti
type Signature derive(Eq, @debug.Debug)
pub fn Signature::empty() -> Self
#alias(extend, deprecated)
pub fn Signature::extend_with(Self, @core.Name, Ty) -> Self
pub fn Signature::lookup(Self, @core.Name) -> Ty?
pub fn Signature::length(Self) -> Int
pub fn Signature::to_array(Self) -> Array[(@core.Name, Ty)]
pub fn Signature::equal(Self, Self) -> Bool
```

The type is abstract: a signature is built only with `empty` and
`extend_with` and cannot be changed afterwards. `empty()` has no constants.
`extend_with(c, ty)` returns a new signature with `c : ty` added; a later
entry for the same name shadows an earlier one, and `lookup` returns the
latest, or `None`. `length` counts the entries, shadowed ones included.
`to_array` returns a fresh array of the entries in insertion order, so
changing it does not change the signature, and `equal` compares the entry
lists.

### `TypeContext`, `TypeContext::empty`, `TypeContext::extend_with`, `TypeContext::lookup`, `TypeContext::length`, `TypeContext::to_array`, `TypeContext::equal`

`TypeContext` assigns types to free variables.

```mbti
type TypeContext
pub impl Eq for TypeContext
pub impl @debug.Debug for TypeContext
pub fn TypeContext::empty() -> Self
#alias(extend, deprecated)
pub fn TypeContext::extend_with(Self, @core.Name, Ty) -> Self
pub fn TypeContext::lookup(Self, @core.Name) -> Ty?
pub fn TypeContext::length(Self) -> Int
pub fn TypeContext::to_array(Self) -> Array[(@core.Name, Ty)]
pub fn TypeContext::equal(Self, Self) -> Bool
```

The functions behave as those of `Signature`, with the same shadowing rule:
the type checker extends the context when it enters a lambda, so the nearest
binder of a name wins. `extend_with` takes amortized constant time when it
extends the longest context built so far from the same empty context, as the
checker does under nested lambdas, so checking under $n$ binders costs $O(n)$
for the extensions; extending a context that has already been extended copies
its entries. `Eq` and `Debug` are written by hand; they compare and show the
entries in insertion order, as before.

```moonbit
test "signatures and contexts" {
  let c = @core.Name::new("c")
  let x = @core.Name::new("x")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let sig = @stlc.Signature::empty().extend_with(c, @stlc.Ty::Arrow(a, a))
  let ctx = @stlc.TypeContext::empty().extend_with(x, a).extend_with(x, @stlc.Ty::Unit)
  assert_eq(sig.lookup(c), Some(@stlc.Ty::Arrow(a, a)))
  assert_eq(ctx.lookup(x), Some(@stlc.Ty::Unit))
  assert_eq(ctx.length(), 2)
  let entries = ctx.to_array()
  entries.push((x, a))
  assert_eq(ctx.length(), 2)
  assert_eq(ctx.lookup(x), Some(@stlc.Ty::Unit))
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
| `EmptyApplication` | an application node, `Apply(head, [])`, has no argument. |
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
arguments, $(\lambda x.\,b)\,a_1 \cdots a_n$, is inferred by inferring the
type of $a_1$ and then typing $b\,a_2 \cdots a_n$ with $x$ given that type.
If $x$ occurs free in $a_2, \dots, a_n$, the parameter is first renamed to a
fresh name, so those arguments keep the types they have in the context. An
application with no arguments, at the root of a spine or nested in its head,
gives `EmptyApplication`.

### `check`

`check` verifies a term against a type.

```mbti
pub fn check(Signature, TypeContext, @syntax.Term[Atom], Ty) -> Result[Unit, TypeError]
```

A lambda checks against an arrow type by checking its body against the
codomain, with the parameter given the domain. A lambda applied directly to
arguments, $(\lambda x.\,b)\,a_1 \cdots a_n$, is checked as `infer` types it,
except that $b\,a_2 \cdots a_n$ is checked against the expected type instead
of inferred: the type of $a_1$ is still inferred, and the parameter is renamed
apart from $a_2, \dots, a_n$ in the same way. So a redex whose result is a
lambda, such as $(\lambda x.\,\lambda y.\,y)\,()$, checks against an arrow
type, also when it is the argument of a function. Every other term is inferred
and compared with `==`; a difference gives `TypeMismatch`. An argument that
is given to a lambda, such as $a_1$, must be inferable: a lambda there gives
`CannotInferLambda`.

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

A redex whose result is a lambda is checked against the expected arrow:

```moonbit
test "check a redex that returns a lambda" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let f = @core.Name::new("f")
  let a = @stlc.Ty::Base(@core.Name::new("A"))
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty()
  // (λx. λy. y) ()
  let redex : @stlc.Term = Apply(Bind(x, Bind(y, Variable(y))), [
    Value(@stlc.Atom::UnitLit),
  ])
  let unit_to_unit = @stlc.Ty::Arrow(@stlc.Ty::Unit, @stlc.Ty::Unit)
  assert_eq(@stlc.check(sig, ctx, redex, unit_to_unit), Ok(()))
  assert_eq(@stlc.infer(sig, ctx, redex), Err(@stlc.TypeError::CannotInferLambda))
  // f ((λx. λy. y) ()) with f : (A -> A) -> A
  let ctx_f = ctx.extend_with(
    f,
    @stlc.Ty::Arrow(@stlc.Ty::Arrow(a, a), a),
  )
  assert_eq(@stlc.infer(sig, ctx_f, Apply(Variable(f), [redex])), Ok(a))
}
```

The trailing arguments of a redex are typed in the context of the redex, not
under its parameter:

```moonbit
test "trailing redex arguments keep their own types" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let b = @stlc.Ty::Base(@core.Name::new("B"))
  let sig = @stlc.Signature::empty()
  let ctx = @stlc.TypeContext::empty().extend_with(x, b)
  // (λx. λy. y) () x, where the last x is the x : B of the context
  let term : @stlc.Term = Apply(Bind(x, Bind(y, Variable(y))), [
    Value(@stlc.Atom::UnitLit),
    Variable(x),
  ])
  assert_eq(@stlc.infer(sig, ctx, term), Ok(b))
  assert_eq(
    @stlc.check(sig, ctx, term, @stlc.Ty::Unit),
    Err(@stlc.TypeError::TypeMismatch(expected=@stlc.Ty::Unit, actual=b)),
  )
}
```

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
gives `NormalForm`.

### `normalize_eta_long`

`normalize_eta_long` checks a term against a type and returns its
beta-normal, eta-long form, computed by typed normalization by evaluation.
The checking pass builds a private typed execution plan, so evaluation and
closure application reuse established types without rechecking or inferring
source subterms. Plan construction preserves the first error reported by
`check`; the public term representation is unchanged.

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

The field `entries` of `Signature` and of `TypeContext` is no longer public;
use `lookup`, `length` and `to_array` instead.
