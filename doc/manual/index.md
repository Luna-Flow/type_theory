# type_theory

`Luna-Flow/type_theory` is the semantic substrate of Luna Flow's symbolic
packages: one definition of names, binding, capture-avoiding substitution and
rewriting, shared by every AST that has variables, plus reference
implementations of the untyped and simply typed lambda calculi with both
small-step reduction and normalization by evaluation. This manual documents
version `0.2.0` on MoonBit 0.10.

## Packages

Every package has an API reference (what you can call), a tutorial (how to use
it) and a design note (the mathematics and the decisions behind it). The
`pkg.generated.mbti` file of each package is the authoritative list of its
public names.

| Package | Contents | Pages |
| --- | --- | --- |
| `core` | names, fresh names, contexts, telescopes, finite renamings | [API](api/core.md) · [tutorial](tutorial/core.md) · [design](design/core.md) |
| `syntax` | the generic named `Term[T]`, free variables, alpha-equivalence, the open `BindingSyntax` trait | [API](api/syntax.md) · [tutorial](tutorial/syntax.md) · [design](design/syntax.md) |
| `substitution` | simultaneous capture-avoiding substitution on `Term[T]` and on any `BindingSyntax` AST | [API](api/substitution.md) · [tutorial](tutorial/substitution.md) · [design](design/substitution.md) |
| `rewrite` | single rewrite steps with rule names and paths, bounded normalization, traces | [API](api/rewrite.md) · [tutorial](tutorial/rewrite.md) · [design](design/rewrite.md) |
| `eval` | named strategies: normal order, applicative order, weak head | [API](api/eval.md) · [tutorial](tutorial/eval.md) · [design](design/eval.md) |
| `debruijn` | De Bruijn terms, conversion, scope checking, shifting, nameless beta | [API](api/debruijn.md) · [tutorial](tutorial/debruijn.md) · [design](design/debruijn.md) |
| `utlc/lambda` | the untyped lambda calculus: beta, eta, normal-order normalization | [API](api/utlc/lambda.md) · [tutorial](tutorial/utlc/lambda.md) · [design](design/utlc/lambda.md) |
| `utlc/nbe` | fuel-bounded untyped normalization by evaluation | [API](api/utlc/nbe.md) · [tutorial](tutorial/utlc/nbe.md) · [design](design/utlc/nbe.md) |
| `stlc` | simply typed lambda calculus: bidirectional checking, eta-long typed NbE | [API](api/stlc.md) · [tutorial](tutorial/stlc.md) · [design](design/stlc.md) |
| `adapter` | contract tests for downstream `BindingSyntax` implementations (no public API) | [API](api/adapter.md) · [tutorial](tutorial/adapter.md) · [design](design/adapter.md) |

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

The guide [Semantic architecture](semantics.md) explains how the layers fit
together and how the three normalizers relate.

## Reading paths

**New to the library.** Start with the [syntax tutorial](tutorial/syntax.md),
then [substitution](tutorial/substitution.md) and
[rewrite](tutorial/rewrite.md). These three are enough to manipulate terms
with binders safely.

**Adapting your own AST.** Read the [adapter tutorial](tutorial/adapter.md),
which implements `BindingSyntax` for a small expression language and uses
generic substitution and rewriting on it, then the
[adapter design](design/adapter.md) for the laws your implementation must
satisfy.

**Working with lambda calculi.** Follow [utlc/lambda](tutorial/utlc/lambda.md),
[eval](tutorial/eval.md), [debruijn](tutorial/debruijn.md),
[utlc/nbe](tutorial/utlc/nbe.md) and [stlc](tutorial/stlc.md) in that order.

**Contributors and reviewers.** Read the design pages: they define every
operation mathematically, derive its laws, and state what each package
deliberately does not do. The [correctness checklist](../../CORRECTNESS_CHECKLIST.md)
records the audited invariants and known issues; changes to substitution,
alpha-equivalence, shifting, beta instantiation, quote or fuel accounting must
update it.

## Install

```bash
moon add Luna-Flow/type_theory@0.2.0
```

Then import the packages you need in `moon.pkg`, for example:

```text
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
}
```

The library has no Luna Flow dependencies; `moonbitlang/quickcheck` is used
by its tests only.

## Toolchain

The code requires MoonBit `moonc` 0.10 or newer and builds on all targets
(`wasm-gc`, `wasm`, `js`, `native`). Run the checks from the repository root:

```bash
moon check --target all
./run_test.sh
moon info
```

## Used by

Downstream Luna Flow repositories such as
[luna-poly](https://lunaflow.cn/en/luna-poly/) and
[floating](https://lunaflow.cn/en/floating/) build on these packages; their
own manuals describe how.
