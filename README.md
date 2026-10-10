# type_theory

`Luna-Flow/type_theory` is the binding, substitution, rewriting and evaluation
substrate for Luna Flow symbolic computation. It gives every AST with
variables one definition of names, alpha-equivalence and capture-avoiding
substitution, and ships reference implementations of the untyped and simply
typed lambda calculi, from small-step reduction to normalization by
evaluation.

## Install

```bash
moon add Luna-Flow/type_theory@0.3.0
```

Requires MoonBit `moonc` 0.10 or newer. All targets are supported (`wasm-gc`,
`wasm`, `js`, `native`).

## Example

Substituting $y$ for $x$ in $\lambda y.\,x\,y$ renames the binder instead of
capturing the inserted $y$:

```moonbit
test "capture-avoiding substitution" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let term : @syntax.Term[Int] = Bind(y, Apply(Variable(x), [Variable(y)]))
  let result = @substitution.Substitution::singleton(x, @syntax.Term::Variable(y))
    .apply(term)
  let y1 = @core.Name::new("y_1")
  let expected : @syntax.Term[Int] = Bind(y1, Apply(Variable(y), [Variable(y1)]))
  assert_eq(result, expected)
}
```

with `moon.pkg`:

```text
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
}
```

## Packages

| Package | Contents |
| --- | --- |
| `core` | names, fresh names, contexts, telescopes, finite renamings |
| `syntax` | generic named `Term[T]`, free variables, alpha-equivalence, the open `BindingSyntax` trait |
| `substitution` | simultaneous capture-avoiding substitution for `Term[T]` and any `BindingSyntax` AST |
| `rewrite` | structured single-step rewriting with rule names and paths, bounded normalization, traces |
| `eval` | normal-order, applicative-order and weak-head strategies |
| `debruijn` | De Bruijn terms, conversion, scope checking, shifting, nameless beta reduction |
| `utlc/lambda` | untyped lambda calculus: beta, eta, normal-order normalization |
| `utlc/nbe` | fuel-bounded untyped normalization by evaluation |
| `stlc` | simply typed lambda calculus: bidirectional type checking, eta-long typed NbE |
| `adapter` | contract tests for downstream `BindingSyntax` implementations |

Downstream ASTs implement `BindingSyntax` to get free variables, generic
substitution and generic rewriting without converting to `Term[T]`; domain
evaluation and canonicalization stay in the downstream package.

## Documentation

The manual is published at <https://lunaflow.cn/en/type_theory/>, with Chinese
and Japanese translations. Its English source is
[`doc/manual/index.md`](doc/manual/index.md): an API reference, a tutorial and
a design note (definitions, typing rules and correctness arguments) for every
package. Audited invariants and known issues are listed in
[`CORRECTNESS_CHECKLIST.md`](CORRECTNESS_CHECKLIST.md); release notes are in
[`CHANGELOG.md`](CHANGELOG.md).

## Development

```bash
moon fmt
moon check --target all
./run_test.sh
moon info
```

`./ready_to_pr.sh` runs all of these. See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache-2.0. See [LICENSE](LICENSE).
