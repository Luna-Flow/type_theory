# TYPE_THEORY

`Luna-Flow/type_theory` is the binding, substitution, rewriting, and evaluation
substrate for Luna-Flow symbolic computation.

## Packages

- `core`: names, contexts, telescopes, freshness, and finite renamings.
- `syntax`: generic named `Term[T]` plus the open `BindingSyntax` trait.
- `substitution`: capture-avoiding named and downstream-AST substitution.
- `rewrite`: structured single-step reduction, paths, traces, and bounded loops.
- `eval`: normal-order, applicative-order, weak-head, and full traversal facades.
- `debruijn`: De Bruijn syntax, conversion, scope checking, shifting, and beta.
- `nbe`: lazy, fuel-bounded untyped normalization by evaluation and quote.
- `lambda`: named beta/eta reference calculus.

## Semantic Boundaries

`Term[T]` treats `T` as a closed atom with respect to `type_theory` names. A
domain AST whose own nodes contain variables should implement `BindingSyntax`
and use `GenericSubstitution` and generic rewrite traversal directly.

Generic substitution is simultaneous and one pass. A replacement inserted for
`x` is not recursively substituted again in the same operation. Generic rewrite
traversal accepts arbitrary domain rules; domain-specific evaluation,
canonicalization, and fixed-point policies remain owned by the downstream AST.

Untyped NbE is intentionally bounded because untyped lambda terms may diverge.
It returns `NormalForm`, `FuelExhausted`, or `ScopeFailure`. The operational
small-step reducer remains the public reference semantics and is tested for
normal-form agreement with NbE on terminating examples.

Public APIs report expected validation and scope failures as structured data.
For example, `RuleName::new` returns `Result[RuleName, RuleNameError]`; use
`RuleName::unsafe_new` only when a non-empty name is guaranteed by an internal
invariant, such as a static rule-name literal.

## Development

```bash
moon fmt
moon check --target all
./run_test.sh
moon info
```

See `CORRECTNESS_CHECKLIST.md` for audited invariants and known boundaries.
