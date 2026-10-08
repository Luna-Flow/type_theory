# Semantic architecture

This guide explains how the packages of `type_theory` fit together: which
package defines what, how the three normalizers of the lambda calculus relate,
and how failures are reported. The individual design pages give the
definitions and proofs.

## Layers

The library is built in layers, each defined in terms of the ones below it.

1. **Names** ([core](design/core.md)). A name is a string compared by
   equality; freshness is always relative to an explicit set of used names, so
   every result is deterministic.
2. **Binding syntax** ([syntax](design/syntax.md)). `Term[T]` is named syntax
   with opaque constants, n-ary application and one-variable binders. Free
   variables, alpha-equivalence and capture-avoiding renaming are defined here.
   The trait `BindingSyntax` exposes the same structure for any downstream AST
   through a one-layer view.
3. **Substitution** ([substitution](design/substitution.md)). Simultaneous,
   one-pass, capture-avoiding substitution, with composition and the
   substitution lemma, for `Term[T]` and for every `BindingSyntax` AST.
4. **Rewriting** ([rewrite](design/rewrite.md), [eval](design/eval.md)). A
   rule rewrites a term at its root; a traversal applies it at one position and
   reports the rule and the path; normalizers and traces repeat single steps
   within a step limit. `eval` names the standard strategies.
5. **Calculi** ([utlc/lambda](design/utlc/lambda.md),
   [debruijn](design/debruijn.md), [utlc/nbe](design/utlc/nbe.md),
   [stlc](design/stlc.md)). The untyped lambda calculus in named and nameless
   form, untyped normalization by evaluation, and the simply typed lambda
   calculus.

Downstream ASTs enter at layer 2 by implementing `BindingSyntax` (see the
[adapter design](design/adapter.md)) and then use layers 3 and 4 directly.
Domain rules, canonical forms and fixed-point policies stay in the downstream
package; the substrate fixes none of them.

## One semantics, three normalizers

The untyped lambda calculus has one reference semantics: normal-order
beta(-eta) reduction on named terms, a sequence of single steps produced by
the rewrite layer. Two faster implementations are checked against it.

| Normalizer | Representation | Strategy | Bound | Output |
| --- | --- | --- | --- | --- |
| `@lambda.normalize` | named `Term[T]` | normal order, beta and eta | step limit | beta-eta normal, n-ary spines kept |
| `@debruijn.normalize` | `DbTerm[T]` | normal order, beta | step limit | beta normal, n-ary spines kept |
| `@nbe.normalize` | `DbTerm[T]` | evaluation + readback, call by name | fuel | beta normal, unary applications |

They agree in the following sense. Conversion to De Bruijn form commutes with
beta steps up to alpha-equivalence ([debruijn design](design/debruijn.md)), so
the named and nameless reducers take corresponding steps. NbE is sound for
beta and realizes the same normalizing strategy
([utlc/nbe design](design/utlc/nbe.md)). Because beta reduction is confluent,
whenever two of them return a beta normal form for the same term, the results
coincide after conversion and after flattening application spines. Eta is
only part of the named reducer.

For typed terms, [stlc](design/stlc.md) adds a fourth normalizer:
type-directed NbE, which needs no bound and returns beta-normal, eta-long
forms, and therefore decides beta-eta equality of well-typed terms (eta for
function types).

## Failure reporting

Expected failures at public boundaries are values, never aborts:

- invalid input data is reported in `Result` types, for example
  `RuleName::new("")` returns `Err(RuleNameError::Empty)`, and type errors are
  `TypeError` values;
- index errors in De Bruijn terms are `ScopeError` values, carried by
  `DbStepResult`, `DbNormalizationResult` and the NbE results;
- running out of steps or fuel is an ordinary outcome
  (`StepLimitReached`, `FuelExhausted`) that reports the work done.

Aborting functions are marked `unsafe_` (`RuleName::unsafe_new`) and are meant
for values whose validity is evident, such as literals. Internal assertions,
such as the fresh-name check in substitution, are unreachable by the lemmas of
the corresponding design page.

## Known boundaries

- `Term[T]` treats `T` as closed: constants are never searched for variables.
- Generic substitution is applied once; inserted replacements are not visited
  again.
- Untyped normalization is not total: `StepLimitReached` and `FuelExhausted`
  are expected for divergent terms.
- The simply typed calculus has base types, `Unit` and arrows only, and no
  eta law for `Unit`.

The [correctness checklist](../../CORRECTNESS_CHECKLIST.md) lists the audited
invariants, their evidence and the known issues.
