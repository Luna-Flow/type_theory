# adapter API

## Purpose

The `adapter` package has no public items. It is a contract-test package: its
white-box tests define a small downstream-style AST, implement
`@syntax.BindingSyntax` for it, and check that generic substitution and
generic rewriting behave as documented on an AST that is not `Term[T]`. Its
generated interface is empty:

```mbti
package "Luna-Flow/type_theory/adapter"

// Values

// Errors

// Types and methods

// Type aliases

// Traits
```

The interface you implement to adapt your own AST is
[`@syntax.BindingSyntax`](syntax.md); the algorithms you then get
are [`@syntax.generic_free_variables`](syntax.md),
[`@substitution.GenericSubstitution`](substitution.md) and
[`@rewrite.generic_top_down_once`](rewrite.md). The
contract is explained in the [adapter design](../design/adapter.md), and the
[adapter tutorial](../tutorial/adapter.md) builds an adapter step by step.

## Importing

There is nothing to import from `adapter`. To adapt your own AST, import the
packages that hold the trait and the generic algorithms:

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
  "Luna-Flow/type_theory/rewrite",
}
```

## What the tests check

The test file `src/adapter/poly_adapter_wbtest.mbt` uses a private AST with
four node kinds: integer literals (projected as `Opaque`), variables, an n-ary
sum node (projected as `Apply`) and a scope node (projected as `Bind`). It
checks that

- `GenericSubstitution::apply_once` substitutes simultaneously and in one
  pass: $\{x \mapsto y,\ y \mapsto 2\}$ applied to $x + y$ gives $y + 2$;
- substitution leaves variables outside its domain in place (partial
  evaluation);
- `generic_top_down_once` finds a redex inside an argument, rebuilds the
  parent through the trait constructors, and reports the path
  `[ApplyArgument(0)]`.
