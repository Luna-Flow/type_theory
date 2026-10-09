# Correctness Checklist

Last audited: 2026-10-09

| Area | Status | Evidence | Contract |
| --- | --- | --- | --- |
| Named free variables | Correct | nested binder tests | bound occurrences are excluded |
| Alpha-equivalence | Correct | shadowing, QuickCheck reflexivity on `Int` payloads, `NaN` payload test (#15) | binder names are irrelevant; payloads are compared with `T`'s `==`, so the relation is an equivalence exactly when that `==` is |
| Named substitution | Correct | nested binder, range, domain collision regressions | simultaneous and capture-avoiding |
| Generic AST substitution | Correct | downstream adapter tests | inserted replacements are not revisited |
| Structured reduction | Correct | path and trace tests | one call contracts at most one redex |
| Named/De Bruijn conversion | Correct | both round-trip laws | named round trip is alpha-equivalent |
| De Bruijn scope | Correct | dangling and negative index tests, reducer scope regressions (#3) | invalid indices return `ScopeError`; `reduce_once` and `normalize` validate their input |
| Shift and instantiation | Correct | nested binder beta tests, downward-shift capture regressions (#9) | standard cutoff-based shifting; a free index that would fall below the cutoff returns `NegativeShift` |
| De Bruijn scope | Correct | dangling and negative index tests, reducer scope regressions (#3, #16) | invalid indices return `ScopeError`; `reduce_once` and `normalize` validate their input before any step |
| Shift and instantiation | Correct | nested binder beta tests | standard cutoff-based shifting |
| De Bruijn small-step | Correct | path, normalization and empty-application tests (#2) | leftmost-outermost beta; `Apply(h, [])` is read as `h` |
| UTLC untyped NbE | Correct within fuel contract | small-step agreement, lazy argument, Omega tests | beta-normalization may exhaust fuel |
| STLC bidirectional typechecking | Correct | typing, rejection, shadowing and trailing-argument capture tests (#1) | inference is syntax-directed and lambdas check against arrows; a redex parameter is renamed apart from trailing arguments |
| STLC typed eta-long NbE | Correct | eta-expansion, open neutral, beta/eta, and curried redex spine tests (#7) | well-typed STLC terms normalize by type-directed readback |
| Custom AST integration | Contract tested | mock downstream AST | domain canonicalization remains downstream |

## Known Boundaries

- `Term[T]` assumes `T` is closed with respect to shared names.
- `alpha_equal` is the payload equality lifted through binders. With a
  non-reflexive `==`, such as `Double` with `NaN`, a term is not alpha-equal
  to itself.
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
- The small-step reducers keep empty applications `Apply(h, [])`. Eta
  normalizing the beta normal form agrees with `@lambda.normalize` only after
  they are erased, and only for terms with unary spines (#16).
- STLC typed NbE is eta-long for arrow types only; the eta law for `Unit` is
  not implemented.

## Known Issues

None open. Fixed on 2026-10-09:

- STLC redex inference typed the trailing arguments `a2 ... an` of
  `(λx. b) a1 a2 ... an` with the parameter `x` in scope, so `check` accepted
  `(λx. λy. y) () x` at `Unit` under `x : B` (#1). The parameter is now renamed
  apart from the trailing arguments.
- Empty applications `Apply(h, [])` hid a redex from the small-step reducers
  while NbE read them as `h` (#2). All normalizers now read them as `h`;
  `stlc` rejects them anywhere in a spine.
- `@debruijn.reduce_once` and `@debruijn.normalize` did not validate scope
  (#3). Both now return `ScopeFailure` for ill-scoped input.
- `@debruijn.shift` with a negative `delta` moved a free index below the
  cutoff, where an enclosing binder captured it: `shift(Bind(Bound(1)), -1, 0)`
  returned `Ok(Bind(Bound(0)))` (#9). It now returns `NegativeShift`.
- STLC typed NbE typed a redex head without flattening the spine, so
  `normalize_eta_long` rejected `((λx. λy. y) ()) x` and
  `(λx. (λy. λz. z) x) () v`, which `check` accepts, with `CannotInferLambda`
  (#7). The evaluator now flattens the spine and follows redex bodies as
  `infer` does.
