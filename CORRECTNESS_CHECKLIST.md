# Correctness Checklist

Last audited: 2026-06-16

| Area | Status | Evidence | Contract |
| --- | --- | --- | --- |
| Named free variables | Correct | nested binder tests | bound occurrences are excluded |
| Alpha-equivalence | Correct | shadowing and QuickCheck reflexivity | binder names are irrelevant |
| Named substitution | Correct | nested binder, range, domain collision regressions | simultaneous and capture-avoiding |
| Generic AST substitution | Correct | downstream adapter tests | inserted replacements are not revisited |
| Structured reduction | Correct | path and trace tests | one call contracts at most one redex |
| Named/De Bruijn conversion | Correct | both round-trip laws | named round trip is alpha-equivalent |
| De Bruijn scope | Correct | dangling and negative index tests | invalid indices return `ScopeError` |
| Shift and instantiation | Correct | nested binder beta tests | standard cutoff-based shifting |
| De Bruijn small-step | Correct | path and normalization tests | leftmost-outermost beta |
| UTLC untyped NbE | Correct within fuel contract | small-step agreement, lazy argument, Omega tests | beta-normalization may exhaust fuel |
| STLC bidirectional typechecking | Correct | typing, rejection, and shadowing tests | inference is syntax-directed and lambdas check against arrows |
| STLC typed eta-long NbE | Correct | eta-expansion, open neutral, and beta/eta tests | well-typed STLC terms normalize by type-directed readback |
| Custom AST integration | Contract tested | mock downstream AST | domain canonicalization remains downstream |

## Known Boundaries

- `Term[T]` assumes `T` is closed with respect to shared names.
- UTLC NbE is not total; `FuelExhausted` is expected for divergent terms.
- Generic rewrite traversal currently provides pre-order single-step semantics;
  additional strategies must preserve the one-redex contract.
- STLC operational normalization remains step-bounded because it intentionally
  reuses the UTLC named lambda reducer as the reference semantics.
- STLC v1 covers only simply typed lambda calculus with `Unit`, base types,
  arrows, and typed constants from a signature.
