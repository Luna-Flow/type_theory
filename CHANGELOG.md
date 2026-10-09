# Changelog

All notable changes to `Luna-Flow/type_theory` are recorded here.

## Unreleased

### Changed

- Migrated to MoonBit 0.10 (`moonc` 0.10 or newer is required).
- `moon.mod` declares the source directory with `source = "src"` instead of
  `options(source: ...)`.
- Trait methods that were implicitly promoted to methods are now promoted
  explicitly in each package's `extends.mbt`: `equal` on every type deriving
  `Eq`, and `compare` and `hash` on `Name` and `RuleName`. These now appear in
  the generated interfaces.
- Test fixtures and blackbox tests follow the 0.10 rules: the adapter test AST
  is `priv`, and blackbox tests qualify package names.
- `@hashset.from_array` calls were replaced by the `@hashset.HashSet([..])`
  constructor.
- `debruijn`: `ScopeError` has a new case `NegativeCutoff(cutoff~ : Int)`,
  returned by `shift` for a negative cutoff. Downstream exhaustive matches on
  `ScopeError` need a new arm (#10).
- **BREAKING:** the types that hold an array are now abstract, so their
  fields are no longer accessible outside their package (#14):
  - `core`: `Context` (`names`), `Telescope` (`entries`), `Renaming`
    (`entries`). Use `Context::to_array`, `length`, `contains`;
    `Telescope::to_array`, `length`; and the new `Renaming::to_array`,
    `Renaming::length`.
  - `substitution`: `Substitution` and `GenericSubstitution` (`entries`). Use
    `get` and the new `to_array` and `length` on both types.
  - `stlc`: `Signature` and `TypeContext` (`entries`). Use `lookup`,
    `to_array` and the new `length` on both types.
  - `rewrite`: `ReductionPath` (`frames`) and `ReductionTrace` (`initial`,
    `steps`, `result`). Use `ReductionPath::to_array` and the new
    `ReductionPath::length`, and `ReductionTrace::initial`, `steps`,
    `result`.
  - `utlc/nbe`: `Semantic` (`inner`). Its payload type `SemanticInner` was
    already opaque and is now private, so nothing changes for callers that
    only used the `eval`, `reflect_*` and `quote` functions.

  Every `to_array` (and `ReductionTrace::steps`) returns a fresh array.
  Struct literals and field access on these types no longer compile outside
  their package.

### Deprecated

- `Context::extend`, `Telescope::extend` (in `core`) and `Signature::extend`,
  `TypeContext::extend` (in `stlc`): `extend` is now a reserved word. Use
  `extend_with`; the old names remain as deprecated aliases.
- The implicit method forms `not_equal`, `op_lt`, `op_le`, `op_gt`, `op_ge`,
  `hash_combine` and `to_repr` are hidden and deprecated; use the operators,
  the traits and `Repr(x)`.
- The method forms of `BindingSyntax` on `Term` (`term.project()`,
  `Term::variable`, `Term::apply`, `Term::bind`) are hidden and deprecated; use
  `@syntax.BindingSyntax::project(term)` and the `Term` constructors.

### Fixed

- `stlc`: `infer` and `check` typed the trailing arguments `a2 ... an` of a
  redex `(λx. b) a1 a2 ... an` with the parameter `x` in scope, so a free `x`
  in those arguments was captured and the checker could accept a wrong type.
  The parameter is now renamed apart from the trailing arguments, in the
  checker and in the typed NbE evaluator (#1).
- `utlc/lambda`, `debruijn`: an empty application `Apply(h, [])` is now read
  as `h` by `beta_rule`, `eta_rule` and `@debruijn.reduce_once`, as `utlc/nbe`
  already did. Before, it hid a redex in its head position, so the small-step
  and NbE normalizers disagreed on terms such as
  `Apply(Apply(Bind(Bound(0)), []), [Free(a)])`. `stlc` now rejects empty
  applications nested in the head of a spine with `EmptyApplication`, as it
  already did at the root (#2).
- `debruijn`: `reduce_once` and `normalize` now validate their input and
  report an ill-scoped term through their `ScopeFailure` case. Before, a
  negative index outside the contracted redex was skipped (`Bind(Bound(-1))`
  was a normal form) and a dangling index was shifted silently
  (`(λ. 5) 1` reduced to `Bound(4)`) (#3).
- `debruijn`: `shift` with a negative `delta` now returns `NegativeShift` when
  a free index would fall below the cutoff. Before, only a negative result was
  rejected, so a free index could be captured by an enclosing binder:
  `shift(Bind(Bound(1)), -1, 0)` returned `Ok(Bind(Bound(0)))`, the identity.
  `instantiate` and the reducers never produced such a shift (#9).
- `debruijn`: `shift` now rejects a negative `cutoff` with
  `NegativeCutoff(cutoff~)`, whatever the term. Before, it was accepted, so
  indices bound inside the term were shifted as if free:
  `shift(Bind(Bound(0)), 1, -1)` returned `Ok(Bind(Bound(1)))`. `instantiate`
  and the reducers only use cutoff `0` (#10).
- `stlc`: `normalize_eta_long` rejected with `CannotInferLambda` some terms
  that `check` accepts: a redex with a curried head such as
  `((λx. λy. y) ()) x`, and a redex whose body is itself a redex consuming the
  outer arguments, such as `(λx. (λy. λz. z) x) () v`. The typed evaluator
  now flattens the application spine before typing its head and follows redex
  bodies the same way `infer` does, so it accepts exactly the terms `check`
  accepts (#7).
- `stlc`: `check` rejected with `CannotInferLambda` well-typed redexes whose
  result is a lambda in checking position, such as `(λx. λy. y) ()` at
  `Unit -> Unit` and `f ((λx. λy. y) ())` at `A` under
  `f : (A -> A) -> A`: the redex rule existed only in inference mode, so the
  lambda left after the arguments were used up had to be inferred. `check`
  now has a checking-mode redex rule: it infers the first argument, renames
  the parameter apart from the trailing arguments as in #1, and checks the
  rest of the spine against the expected type. `normalize_checked` and
  `normalize_eta_long` accept the same terms (#8).
- `eval`: `ApplicativeOrder` now reads application spines curried, so it
  takes the same steps on `Apply(f, [a1, a2])` and on
  `Apply(Apply(f, [a1]), [a2])`. Before, it was `@rewrite.bottom_up_once`,
  which tries every argument before the application: for
  `Apply(λx. b, [a1, a2])` it reduced inside `a2` before the redex
  `(λx. b) a1`, which the nested encoding contracts first. After argument
  `ai` it now tries the rule on the whole application if the rule applies to
  the prefix `Apply(h, [a1 .. ai])`; only real positions are rewritten, and
  `@rewrite.bottom_up_once` keeps its n-ary post-order (#11).
- `utlc/nbe`: evaluation and readback no longer grow the host stack with the
  fuel spent. They recursed once per pending step, so on js, wasm and wasm-gc
  a divergent term such as `(λ. 0 0) (λ. 0 0)` overflowed the stack with a
  budget of a few million units instead of returning `FuelExhausted`. Both
  now run as loops over an explicit stack of frames in the heap, bounded by
  the budget; results and `consumed` are unchanged (#12).
- `core`, `substitution`, `stlc`, `rewrite`: values documented as immutable
  could be changed through their public array fields, for example
  `s.entries.push((x, t))` gave a substitution two entries for `x`, so `s`
  and `s.then(empty)` disagreed, and `ctx.names.push(x)` grew a `Context` in
  place. The fields are now hidden (see Changed) (#14).
- Documentation: `@syntax.Term` and `@debruijn.DbTerm` values are shared, not
  copied, by substitutions, traces and the reducers; the API pages now say
  that the argument array of `Apply` must be treated as immutable.
- Stack safety (#13, first part): `syntax`, `core`, `substitution`, `debruijn`
  and `utlc/nbe` no longer recurse on the host stack along the nesting depth
  of the input, so terms nested 100,000 deep work on js, wasm and wasm-gc as
  they do on native. Traversals keep their pending work on a heap array;
  results, error order, reduction paths and fuel accounting are unchanged.
  `Term` and `DbTerm` use a hand-written structural `Eq` instead of the
  derived one. `from_named`, `to_named` and the NbE environments also lost
  quadratic costs on long binder chains. Derived `Debug` of deep terms still
  recurses, and `rewrite`, `eval`, `utlc/lambda` and `stlc` are not converted
  yet.

### Documentation

- Documentation rewritten: API reference, tutorial and design note for every
  package, a semantic architecture guide, and a Typst note with the De Bruijn
  index lemmas, with zh_CN and ja_JP translations.
- `CORRECTNESS_CHECKLIST.md` records the spine shape of NbE normal forms and
  the missing unit eta law, and lists the issues fixed above.
- The manual follows the Luna Flow documentation standard: API pages open
  with Purpose and Importing sections and give every public item a heading,
  tutorials start with an "I want to / Use" table, design pages state their
  constraints, and the overview lists the exported items and the release
  checks.
- Logic review of the manual: the substitution laws (free variables,
  restriction, alpha-invariance, composition) are now proved through the
  nameless reading of terms, replacing an invalid alpha-invariance step and a
  composition argument that overlooked binders inside replacements. The
  agreement of the three untyped normalizers is restated (the named
  normalizer also contracts eta), and the fuel-determinism argument of NbE is
  spelled out.
- The manual describes the fixed behaviour of the three bugs above, and the
  STLC soundness theorem is now unconditional.
- The precondition of a De Bruijn shift is stated correctly in the API page,
  the design page and the Typst note: no free index `i >= c` with `i + d < c`,
  instead of "no index becomes negative". The cancellation and safe
  instantiation proofs check the cutoff accordingly (#9).
- `debruijn`: the API page, the design page and the Typst note state that
  `shift` requires `cutoff >= 0` and document `NegativeCutoff` (#10).
- `syntax`: the manual no longer states that `alpha_equal` is always an
  equivalence. It compares payloads with `T`'s `==`, so it is an equivalence
  exactly when that `==` is one, and it is alpha-equivalence when `==` is the
  identity; with `Double`, a `NaN` payload is not alpha-equal to itself
  (#15).
- `utlc/lambda`, `debruijn`: the manual no longer claims that eta-normalizing
  the beta normal form gives a term alpha-equivalent to `@lambda.normalize`.
  The two agree modulo `Apply(h, []) = h` for terms with unary spines, now
  stated and proved in the design note, but not literally. `ScopeFailure` of
  `DbStepResult` is described as the result of input validation, not of an
  error met while contracting a redex (#16).
