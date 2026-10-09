# Correctness Checklist

Last audited: 2026-10-09

| Area | Status | Evidence | Contract |
| --- | --- | --- | --- |
| Named free variables | Correct | nested binder tests | bound occurrences are excluded |
| Alpha-equivalence | Correct | shadowing, QuickCheck reflexivity on `Int` payloads, `NaN` payload test (#15) | binder names are irrelevant; payloads are compared with `T`'s `==`, so the relation is an equivalence exactly when that `==` is |
| Named substitution | Correct | nested binder, range, domain collision regressions | simultaneous and capture-avoiding |
| Generic AST substitution | Correct | downstream adapter tests | inserted replacements are not revisited |
| Structured reduction | Correct | path and trace tests; n-ary versus curried spine regression and lockstep property test for every strategy (#11) | one call contracts at most one redex; `ApplicativeOrder` reads spines curried |
| Named/De Bruijn conversion | Correct | both round-trip laws | named round trip is alpha-equivalent |
| De Bruijn scope | Correct | dangling and negative index tests, reducer scope regressions (#3, #16) | invalid indices return `ScopeError`; `reduce_once` and `normalize` validate their input before any step |
| Shift and instantiation | Correct | nested binder beta tests, downward-shift capture regressions (#9), negative cutoff regressions (#10) | standard cutoff-based shifting; a free index that would fall below the cutoff returns `NegativeShift`; a negative cutoff returns `NegativeCutoff` |
| De Bruijn small-step | Correct | path, normalization and empty-application tests (#2) | leftmost-outermost beta; `Apply(h, [])` is read as `h` |
| UTLC untyped NbE | Correct within fuel contract | small-step agreement, lazy argument, Omega tests, 30M-unit divergence tests on every backend and exact-cost tests (#12) | beta-normalization may exhaust fuel; evaluation and readback use a constant host stack |
| STLC bidirectional typechecking | Correct | typing, rejection, shadowing and trailing-argument capture tests (#1); checking-mode redex tests on curried and flat spines, nested redexes, capture and ill-typed variants (#8) | inference is syntax-directed and lambdas check against arrows; a redex is typed in either mode by inferring its first argument, and a checked redex checks the rest of its spine against the expected type; a redex parameter is renamed apart from trailing arguments |
| STLC typed eta-long NbE | Correct | eta-expansion, open neutral, beta/eta, curried redex spine tests (#7), and redexes returning a lambda (#8) | well-typed STLC terms normalize by type-directed readback; accepts exactly the terms `check` accepts |
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

Open:

- Deeply nested input terms overflow the host stack on js, wasm and wasm-gc
  (#13).
- Public array fields let callers mutate values documented as immutable (#14).

Fixed on 2026-10-09:

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
- `@debruijn.shift` accepted a negative cutoff, so indices bound inside the
  term were shifted as if free: `shift(Bind(Bound(0)), 1, -1)` returned
  `Ok(Bind(Bound(1)))` (#10). It now returns `NegativeCutoff` for any
  negative cutoff.
- STLC typed NbE typed a redex head without flattening the spine, so
  `normalize_eta_long` rejected `((λx. λy. y) ()) x` and
  `(λx. (λy. λz. z) x) () v`, which `check` accepts, with `CannotInferLambda`
  (#7). The evaluator now flattens the spine and follows redex bodies as
  `infer` does.
- STLC `check` had no checking-mode redex rule, so it rejected
  `(λx. λy. y) ()` at `Unit -> Unit` and `f ((λx. λy. y) ())` at `A` under
  `f : (A -> A) -> A` with `CannotInferLambda` (#8). A checked redex now
  infers its first argument and checks the rest of its spine against the
  expected type; `normalize_eta_long` accepts the same terms.
- `ApplicativeOrder` tried every argument of an n-ary spine before the
  application, so `Apply(λx. b, [a1, a2])` reduced inside `a2` before the
  redex `(λx. b) a1` that the nested encoding contracts first (#11). It now
  follows the curried reading and takes the same steps on both encodings.
- UTLC NbE overflowed the host stack on js, wasm and wasm-gc instead of
  returning `FuelExhausted` when a divergent term was given a large budget
  (#12). Evaluation and readback now keep pending work on a heap stack, so the
  host stack no longer grows with the fuel spent.
