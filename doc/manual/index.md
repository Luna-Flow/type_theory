# type_theory

This manual documents version `0.2.0` of `Luna-Flow/type_theory` on MoonBit 0.10.

## Overview

`Luna-Flow/type_theory` is the semantic substrate of Luna Flow's symbolic
packages: one definition of names, binding, capture-avoiding substitution and
rewriting, shared by every AST that has variables, plus reference
implementations of the untyped and simply typed lambda calculi with both
small-step reduction and normalization by evaluation.

The packages form layers; each depends only on the ones above it:

```text
core
 └─ syntax
     ├─ substitution
     ├─ rewrite ── eval
     │    └─ debruijn ── utlc/nbe
     └─ utlc/lambda (substitution, eval)
          └─ stlc (debruijn, utlc/lambda)
```

Downstream ASTs enter at `syntax` by implementing the trait `BindingSyntax`
and then use generic substitution and rewriting without converting to the
library's own term type. The guide [Semantic architecture](semantics.md)
explains how the layers fit together and how the normalizers relate.

## Install

```bash
moon add Luna-Flow/type_theory@0.2.0
```

Then import the packages you need in your `moon.pkg`, for example:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
}
```

The code needs the MoonBit toolchain 0.10 or later (`moonc` ≥ 0.10) and
builds on all targets (`wasm-gc`, `wasm`, `js`, `native`). The library has no
Luna Flow dependencies; `moonbitlang/quickcheck` is used by its tests only.

## Pages

Every package has an API reference (what you can call), a tutorial (how to use
it) and a design note (the mathematics and the decisions behind it). The
`pkg.generated.mbti` file of each package is the authoritative list of its
public names.

| Part | Tutorial | API | Design |
| --- | --- | --- | --- |
| `core`: names, fresh names, contexts, telescopes, renamings | [tutorial](tutorial/core.md) | [API](api/core.md) | [design](design/core.md) |
| `syntax`: `Term[T]`, free variables, alpha-equivalence, `BindingSyntax` | [tutorial](tutorial/syntax.md) | [API](api/syntax.md) | [design](design/syntax.md) |
| `substitution`: simultaneous capture-avoiding substitution | [tutorial](tutorial/substitution.md) | [API](api/substitution.md) | [design](design/substitution.md) |
| `rewrite`: single steps with rule names and paths, normalization, traces | [tutorial](tutorial/rewrite.md) | [API](api/rewrite.md) | [design](design/rewrite.md) |
| `eval`: normal order, applicative order, weak head | [tutorial](tutorial/eval.md) | [API](api/eval.md) | [design](design/eval.md) |
| `debruijn`: nameless terms, conversion, scope, shifting, beta | [tutorial](tutorial/debruijn.md) | [API](api/debruijn.md) | [design](design/debruijn.md) |
| `utlc/lambda`: untyped lambda calculus, beta and eta | [tutorial](tutorial/utlc/lambda.md) | [API](api/utlc/lambda.md) | [design](design/utlc/lambda.md) |
| `utlc/nbe`: fuel-bounded untyped normalization by evaluation | [tutorial](tutorial/utlc/nbe.md) | [API](api/utlc/nbe.md) | [design](design/utlc/nbe.md) |
| `stlc`: bidirectional type checking, eta-long typed NbE | [tutorial](tutorial/stlc.md) | [API](api/stlc.md) | [design](design/stlc.md) |
| `adapter`: contract tests for downstream `BindingSyntax` ASTs | [tutorial](tutorial/adapter.md) | [API](api/adapter.md) | [design](design/adapter.md) |
| Guide: how the layers fit together | [Semantic architecture](semantics.md) | | |

## Exported items

### Names, terms and substitution

- `core`: `Name`, `fresh_name`, `Context`, `Telescope`, `Renaming`
- `syntax`: `Term`, `free_variables`, `all_names`, `alpha_equal`,
  `Term::rename_free`, `Term::alpha_rename_bound`, `Term::map_values`
- `syntax`, for downstream ASTs: `BindingView`, `BindingSyntax`,
  `generic_free_variables`, `generic_all_names`, `generic_alpha_rename_bound`
- `substitution`: `Substitution`, `GenericSubstitution`, `from_renaming`

### Rewriting and strategies

- `rewrite`: `RuleName`, `RuleNameError`, `ReductionFrame`, `ReductionPath`,
  `StepResult`, `NormalizationResult`, `ReductionTrace`, `top_down_once`,
  `bottom_up_once`, `normalize`, `trace`
- `rewrite`, for downstream ASTs: `GenericStepResult`,
  `GenericNormalizationResult`, `generic_top_down_once`, `generic_normalize`
- `eval`: `Strategy`, `reduce_once`, `evaluate`, `trace`

### Lambda calculi

- `debruijn`: `DbTerm`, `ScopeError`, `from_named`, `to_named`, `validate`,
  `shift`, `substitute_bound`, `instantiate`, `reduce_once`, `normalize`,
  `DbStepResult`, `DbNormalizationResult`
- `utlc/lambda`: `abstraction`, `application`, `beta_rule`, `eta_rule`,
  `beta_eta_rule`, `normalize`
- `utlc/nbe`: `Semantic`, `eval`, `quote`, `normalize`, `reflect_free`,
  `reflect_level`, `EvaluationResult`, `QuoteResult`, `NbeResult`
- `stlc`: `Atom`, `Term`, `Ty`, `Signature`, `TypeContext`, `TypeError`,
  `infer`, `check`, `normalize_checked`, `normalize_eta_long`

### Deprecated

- `Context::extend`, `Telescope::extend` (`core`) and `Signature::extend`,
  `TypeContext::extend` (`stlc`): use `extend_with`. `extend` is a reserved
  word since MoonBit 0.10; the old names remain as deprecated aliases.

> [!WARNING]
> `@stlc.check` can accept a term at a wrong type when a lambda applied to
> several arguments has a parameter that occurs free in a later argument.
> The [stlc API](api/stlc.md) describes the case and how to avoid it.

## Where to read next

- New to the library: start with the [syntax tutorial](tutorial/syntax.md),
  then [substitution](tutorial/substitution.md) and
  [rewrite](tutorial/rewrite.md). These three are enough to manipulate terms
  with binders safely. For the lambda calculi, continue with
  [utlc/lambda](tutorial/utlc/lambda.md), [eval](tutorial/eval.md),
  [debruijn](tutorial/debruijn.md), [utlc/nbe](tutorial/utlc/nbe.md) and
  [stlc](tutorial/stlc.md) in that order.
- Using it in a library: read the [adapter tutorial](tutorial/adapter.md),
  which implements `BindingSyntax` for a small expression language and uses
  generic substitution and rewriting on it. Keep the API pages at hand, and
  the [adapter design](design/adapter.md) for the laws your implementation
  must satisfy.
- Contributing: read the design pages; they define every operation
  mathematically, derive its laws, and state what each package deliberately
  does not do. The [correctness checklist](../../CORRECTNESS_CHECKLIST.md)
  records the audited invariants and known issues; changes to substitution,
  alpha-equivalence, shifting, beta instantiation, quote or fuel accounting
  must update it.

## Validation

Recommended release checks, from the repository root:

```bash
moon check --target all
./run_test.sh
moon info
```

`./run_test.sh` runs `moon test` on `wasm-gc`, `js`, `native` and `wasm`.

## Used by

Downstream Luna Flow repositories such as
[luna-poly](https://lunaflow.cn/en/luna-poly/) and
[floating](https://lunaflow.cn/en/floating/) build on these packages; their
own manuals describe how.
