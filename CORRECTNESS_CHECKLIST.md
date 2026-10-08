# Correctness Checklist

Last audited: 2026-10-09

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
| STLC bidirectional typechecking | Known issue | typing, rejection, and shadowing tests | inference is syntax-directed and lambdas check against arrows; unsound for the redex case below |
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
- UTLC NbE reads applications back as unary `Apply` nodes, while the De Bruijn
  small-step reducer keeps n-ary spines; agreement holds after spine
  flattening.
- STLC typed NbE is eta-long for arrow types only; the eta law for `Unit` is
  not implemented.

## Known Issues

- STLC redex inference (`(λx. b) a1 a2 ... an` with `n >= 2`) types the
  arguments `a2 ... an` in a context that already binds the parameter `x`. If
  such an argument has a free variable named `x`, `infer` uses the parameter's
  type. This makes `check` unsound: with `x : B`, `check` accepts
  `(λx. λy. y) () x` at `Unit` (its only type is `B`) and rejects it at `B`,
  and `normalize_checked` at `Unit` returns `x`. `normalize_eta_long` rejects
  the term at both types. Found while documenting (2026-10-08), soundness
  impact confirmed 2026-10-09; not yet fixed.
- An empty application `Apply(h, [])` is never a beta redex for
  `@lambda.beta_rule` or `@debruijn.reduce_once` and hides a redex in its head
  position, while `@nbe.normalize` evaluates it as `h`. The small-step and NbE
  normalizers therefore disagree on terms such as
  `Apply(Apply(Bind(Bound(0)), []), [Free(a)])`. Documented 2026-10-09; the
  constructors in `utlc/lambda` never build empty applications.
- `@debruijn.reduce_once` and `@debruijn.normalize` do not validate scope: a
  negative index outside the contracted redex is ignored (`Bind(Bound(-1))`
  is reported as a normal form) and a dangling index is shifted like a free
  one. Callers must `validate` untrusted input. Documented 2026-10-09.
