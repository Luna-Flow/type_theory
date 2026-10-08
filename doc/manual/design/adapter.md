# adapter design

## Design goal

Downstream repositories have their own ASTs (polynomial expressions, numeric
expression trees, typed cores) and should not have to convert them to
`Term[T]` to get correct binding semantics. The adapter design fixes how such
an AST connects to the shared algorithms through `@syntax.BindingSyntax`, what
an implementation must guarantee, and how that guarantee is tested. The
`adapter` package holds the reference contract test; it has no public API.

## Mathematical background

### Views

Let $N$ be the downstream AST and

$$
F(X) = 1 + \mathcal{N} + X \times X^{*} + \mathcal{N} \times X
$$

the signature functor of binding syntax, whose summands are `Opaque`,
`Variable`, `Apply` and `Bind` of `BindingView[X]`. An adapter consists of a
*projection* (coalgebra) and *constructors* (a partial algebra):

$$
\pi : N \to F(N) \quad (\texttt{project}), \qquad
\kappa : F(N) \setminus 1 \to N \quad (\texttt{variable},\ \texttt{apply},\ \texttt{bind}).
$$

### The view laws

For all names $x$, nodes $h, b, n$ and arrays $\bar a$:

$$
\begin{aligned}
\text{(V1)}\quad & \pi(\kappa(\mathsf{Variable}(x))) = \mathsf{Variable}(x), \\
\text{(V2)}\quad & \pi(\kappa(\mathsf{Apply}(h, \bar a))) = \mathsf{Apply}(h, \bar a), \\
\text{(V3)}\quad & \pi(\kappa(\mathsf{Bind}(x, b))) = \mathsf{Bind}(x, b), \\
\text{(V4)}\quad & \pi(n) \ne \mathsf{Opaque} \implies \kappa(\pi(n)) \equiv n, \\
\text{(V5)}\quad & \pi(n) = \mathsf{Opaque} \implies n \text{ contains no variable occurrence}, \\
\text{(V6)}\quad & \pi(n) = \mathsf{Apply}(h, \bar a) \text{ or } \mathsf{Bind}(x, h) \implies h, a_i \text{ are smaller than } n.
\end{aligned}
$$

(V1)–(V3) say that constructors build what the projection reports; (V4) says
that rebuilding a projected node gives back an equivalent node ($\equiv$ is the
downstream notion of equality, often `==`); (V5) is the "closed atom" contract
of `Opaque`; (V6) makes structural recursion through $\pi$ terminate. Under
(V1)–(V4), $\pi$ restricted to non-opaque nodes and $\kappa$ are mutually
inverse, so $N$ minus its opaque nodes is isomorphic to one layer of binding
syntax over $N$.

### Why the laws suffice

Every generic algorithm is defined by structural recursion through $\pi$ and
rebuilds with $\kappa$. For each algorithm, the proof of its law for `Term[T]`
in the [syntax](syntax.md) and [substitution](substitution.md) designs uses
exactly two facts about `Term`: that pattern matching sees the constructors,
and that constructors build those same nodes. (V1)–(V4) state these facts for
$N$. (V5) justifies treating opaque nodes as having
$\mathrm{FV} = \mathrm{names} = \varnothing$, and (V6) gives well-founded
induction. Hence, for a lawful adapter:

- `generic_free_variables` and `generic_all_names` compute $\mathrm{FV}$ and
  $\mathrm{names}$ of the node read as binding syntax;
- `generic_alpha_rename_bound` satisfies the alpha step;
- `GenericSubstitution::apply_once` is simultaneous and capture-avoiding
  (Lemmas 1–3 of the substitution design);
- `generic_top_down_once` satisfies the one-redex contract and the normal-form
  lemma of the [rewrite design](rewrite.md).

## Design decisions

### A view trait rather than conversion

**Problem.** A downstream AST could be converted to `Term[T]`, processed, and
converted back.

**Options.** Conversion functions; a generic traversal library (a functor
with `map`); a view trait.

**Choice.** A view trait with one projection and three constructors. Unlike
conversion, it allocates only the nodes an algorithm rebuilds, and it keeps
the downstream node kinds: a sum node projected as `Apply` is rebuilt as a sum
node, not as an application. Unlike a general functor, it needs no
higher-kinded types, which MoonBit does not have: the view is the concrete
type `BindingView[N]`.

### Several node kinds may share one view case

The view distinguishes only what binding needs. A downstream AST with sums,
products and powers may project all three as `Apply`; the constructor
`apply(head, args)` must then rebuild the right kind, which it can only do if
the kind is recoverable from `head` or the arguments. The contract test's
sum node is the simplest case: a single `Apply`-like node kind. When several
kinds must be rebuilt, encode the operator in the head (for example as an
opaque operator node), so that (V4) holds.

### Opaque nodes are atoms

`Opaque` nodes are returned unchanged and never searched for variables. This
is the same contract as `Value(T)` in `Term[T]` and is what lets literals of
any type (integers, floats, rational numbers) take part without a trait of
their own. A node that does contain variables must not project as `Opaque`
(V5); otherwise substitution silently skips them.

### Domain policy stays downstream

The trait gives binding structure only. Canonical forms, evaluation of
operators, simplification order and fixed-point iteration are rules and
strategies supplied by the downstream package through
[rewrite](rewrite.md); the substrate fixes none of them. This keeps the
library free of any particular algebra and lets each downstream package
document its own policy.

### Bridging variable types

A downstream variable type converts to `@core.Name` by an injective map
(distinct variables to distinct names). Injectivity is what makes name
equality agree with variable identity, so that freshness and capture checks
are correct for the downstream variables.

## Correctness / invariants

The contract test `src/adapter/poly_adapter_wbtest.mbt` checks a lawful
adapter for a four-kind AST:

| Property | Check |
| --- | --- |
| simultaneous one-pass substitution | $\{x \mapsto y, y \mapsto 2\}$ on $x + y$ gives $y + 2$ |
| unmapped variables are kept | $\{x \mapsto 3\}$ on $x + y$ gives $3 + y$ |
| rewriting rebuilds through constructors | $1 + (0 + 2) \to 1 + 2$ at path `[ApplyArgument(0)]` |

Downstream adapters should add tests of (V1)–(V5) for their own node kinds:
project each constructor's result, rebuild each projected node, and check that
opaque nodes have no free variables.

## Alternatives rejected

- **Making `Term[T]` the only AST.** Rejected because downstream ASTs carry
  invariants (normalized coefficients, typed nodes) that `Term[T]` cannot
  express.
- **A larger view with sorts or multi-binders.** More cases would make every
  adapter and every generic algorithm larger; nested `Bind` nodes express
  multi-binders.
- **Checking the laws at run time.** The laws are equations over all nodes;
  they are tested, not enforced.

## Boundaries

- The trait cannot express binders whose scope is not one child, or nodes
  that bind several names in different children.
- Lawfulness is the implementer's responsibility; an unlawful adapter gets
  undefined results from the generic algorithms.
- The `adapter` package exports nothing; it only tests the contract.
