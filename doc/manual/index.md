# type_theory

This module provides reusable named and De Bruijn binding semantics,
capture-avoiding substitution, structured single-step reduction, and bounded
untyped NbE.

Custom domain ASTs should implement `BindingSyntax` to use one-pass generic
substitution and arbitrary custom rewrite rules. Lambda users may choose named
syntax, De Bruijn small-step reduction, or bounded NbE with quote.

## Packages

| Package | Contents |
| --- | --- |
| `core` | Names, contexts, telescopes, freshness, and finite renamings. |
| `syntax` | Generic named `Term[T]` plus the open `BindingSyntax` trait. |
| `substitution` | Capture-avoiding named and downstream-AST substitution. |
| `rewrite` | Structured single-step reduction, paths, traces, and bounded loops. |
| `eval` | Normal-order, applicative-order, weak-head, and full traversal facades. |
| `debruijn` | De Bruijn syntax, conversion, scope checking, shifting, and beta. |
| `utlc/lambda` | Untyped named beta/eta reference calculus. |
| `utlc/nbe` | Lazy, fuel-bounded untyped normalization by evaluation and quote. |
| `stlc` | Simply typed lambda calculus over the shared substrate, with bidirectional typechecking, checked operational normalization, and typed eta-long normalization by evaluation. |

The generated `pkg.generated.mbti` file of each package is the authoritative
list of its public names and signatures.

## Further reading

- [Semantic design](semantics.md) explains how reduction, NbE, the two syntax
  representations, and failure reporting fit together.
- The [correctness checklist](../../CORRECTNESS_CHECKLIST.md) records the
  audited invariants and known boundaries.
