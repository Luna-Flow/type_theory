# core design

## Design goal

`core` fixes what a variable is for the whole library, so that binding,
substitution, rewriting and type checking in different packages, and in
downstream repositories, agree on one notion of name. It
also provides the one piece of name generation that every capture-avoiding
algorithm needs, and the finite renamings that those algorithms manipulate.

## Constraints

- **Determinism.** No hidden global state: every result, fresh names
  included, is a function of the arguments, so normal forms are reproducible
  across runs and printable as they are.
- **Adoption cost.** A downstream AST must be able to use these names without
  changing its own representation of variables.
- **Sharing.** Values are passed between packages and kept in traces, so they
  must be immutable.

## Mathematical background

### Names as atoms

Let $\mathcal{N}$ be a countably infinite set of *names* (atoms) with
decidable equality. Syntax with binders is built over $\mathcal{N}$; the only
operations on names that the theory needs are equality and the choice of a
name outside a finite set.[^atoms] `Name` realises $\mathcal{N}$ as strings:
two names are equal exactly when their texts are equal, and the strings are
an infinite supply.

[^atoms]: This is the view of nominal techniques (Gabbay and Pitts, "A new approach to abstract syntax with variable binding", 2002): names are atoms with equality only, and every syntactic object has finite support.

### Freshness

A name $a$ is *fresh* for a finite set $U \subseteq \mathcal{N}$ when
$a \notin U$. `fresh_name` is a choice function

$$
\operatorname{fresh}(h, U) =
\begin{cases}
h & \text{if } h \notin U,\\
c_k & \text{otherwise, with } k = \min\{\, k \ge 1 \mid c_k \notin U \,\},
\end{cases}
\qquad c_k = h \mathbin{+\!\!+} \texttt{"\_"} \mathbin{+\!\!+} \operatorname{show}(k).
$$

**Lemma (freshness).** $\operatorname{fresh}(h, U) \notin U$, and the search
stops after at most $|U| + 1$ candidates.

The candidates $c_1, c_2, \dots$ are pairwise distinct strings, so at most
$|U|$ of them lie in $U$. By the pigeonhole principle one of
$c_1, \dots, c_{|U|+1}$ is not in $U$, and the minimum $k$ exists:

$$
\begin{aligned}
|\{\, k \le |U| + 1 \mid c_k \in U \,\}| &\le |U| < |U| + 1 \\
\Longrightarrow\ \exists\, k \le |U| + 1.\ c_k &\notin U .
\end{aligned}
$$

Each candidate costs one hash-set lookup, plus building its string, so the
search makes at most $|U| + 1$ lookups, and exactly one when the hint is
already fresh.

### Renamings

A *renaming* is a function $\rho : \mathcal{N} \to \mathcal{N}$ with finite
domain $\operatorname{dom}\rho = \{\, n \mid \rho(n) \ne n \,\}$. `Renaming`
stores a finite list of pairs and denotes

$$
\rho(n) =
\begin{cases}
m & \text{if } (n, m) \text{ is an entry},\\
n & \text{otherwise.}
\end{cases}
$$

`set` keeps at most one entry per source, so the denotation is well defined.
Renamings with composition form a monoid. `Renaming::then` implements
$\rho \mathbin{;} \sigma = \sigma \circ \rho$, and the identity is
`Renaming::empty`. The monoid laws are laws of the denoted functions, which is what the
composition lemma below establishes; `==` compares entry lists, and two
lists that denote the same function (such as `empty()` and
`singleton(x, x)`) are not `==`.

**Lemma (composition).** For every name $n$,
`r.then(s).apply(n) == s.apply(r.apply(n))`.

`then` first adds, for each entry $(a, b)$ of $\rho$, the entry
$(a, \sigma(b))$, and then, for each entry $(c, d)$ of $\sigma$ with
$\rho(c) = c$, the entry $(c, d)$. Split on $n$:

$$
\begin{aligned}
n \text{ is a source of } \rho:&\quad (\rho;\sigma)(n) = \sigma(\rho(n)) && \text{first loop},\\
n \notin \operatorname{dom}\rho,\ n \text{ a source of } \sigma:&\quad (\rho;\sigma)(n) = \sigma(n) = \sigma(\rho(n)) && \text{second loop},\\
\text{otherwise}:&\quad (\rho;\sigma)(n) = n = \sigma(\rho(n)) && \text{no entry}.
\end{aligned}
$$

The second loop skips every name that $\rho$ moves, so it never overrides
an entry of the first loop with a different value; the only overlap is an
explicit identity entry $(a, a)$ of $\rho$, for which both loops write the
same value $\sigma(a)$. The case "$n$ is a source of $\rho$" includes such
identity entries, which is why it is listed first.

Two further operations serve binders. $\rho \setminus x$ (`without`) is
$\rho$ with $x$ removed from the domain; under a binder for $x$ the free
occurrences of $x$ are a different variable, so the renaming must not touch
them. The *support* $\operatorname{supp}\rho$ is the set of all sources and
targets, and $\operatorname{tgt}\rho$ the set of targets; capture can only
happen when a binder name is a target.

### Contexts and telescopes

A context $\Gamma = x_1, \dots, x_n$ is a finite sequence of names. A
telescope $\Delta = (x_1 : A_1) \dots (x_n : A_n)$ adds an annotation to each
binder, where $A_i$ may depend on $x_1, \dots, x_{i-1}$.[^telescope] Both are
read innermost last, and a later occurrence of a name shadows an earlier one.

[^telescope]: N. G. de Bruijn, "Telescopic mappings in typed lambda calculus", Information and Computation 91, 1991.

## Design decisions

### Names are strings, not unique identifiers

**Problem.** Binding algorithms need names with equality and a supply of
fresh names. The common implementations are strings, globally unique integers
from a counter (gensym), and pairs of a string and a counter.

**Options.** A global counter makes freshness trivial but is hidden mutable
state, and its output depends on everything that ran before. A pair of string
and counter needs a convention for printing. Plain strings need an explicit
"used" set for freshness.

**Choice.** `Name` is a plain string, and freshness is relative to an explicit
set. This follows the Luna Flow rule of no hidden global state: the result of
`fresh_name(hint, used)` depends only on its arguments, so normal forms such as
`λy_1. y y_1` are reproducible across runs and printable as they are. Callers
pay for this by computing the set of used names, which the capture-avoiding
algorithms in `syntax` and `substitution` do from the terms themselves.

### Suffix search keeps hints readable

`fresh_name` keeps the hint when it is free and otherwise appends the smallest
numeric suffix that works. The alternative, always returning a new synthetic
name, would make every substitution result unreadable. The suffix scheme can
collide with user names of the form `x_1`; this is harmless because such names
are in the used set and are skipped.

### Persistent values by copying

`Context`, `Telescope` and `Renaming` are immutable records over arrays.
The types are abstract, so the arrays can be reached only inside the
package: `from_array` copies its argument, `to_array` returns a copy, and
every update builds a new array, which costs $O(n)$. The alternative, a
persistent list or tree, would make updates cheaper but the sizes involved are
the number of binders in scope, which is small for the intended use. Copying
keeps the representation simple and the values safe to share.

### Renamings are not required to be injective

A renaming that maps two names to one target is useful (it identifies
variables) and is allowed. The capture-avoiding operations therefore do not
rely on injectivity: they freshen a binder whenever it is a target, see the
[syntax design](syntax.md).

## Correctness and invariants

- `fresh_name(h, U) ∉ U`, and `fresh_name(h, U) = h` when `h ∉ U` (freshness lemma).
- `Renaming::set` keeps at most one entry per source, and because the type
  is abstract no other code can add an entry; `apply` therefore denotes a
  function.
- `r.then(s)` denotes $\sigma \circ \rho$ (composition lemma); `empty` is a
  two-sided identity for `then` as functions.
- `r.without(x).apply(x) == x` and `r.without(x).apply(n) == r.apply(n)` for
  `n != x`.
- Every operation returns a new value; no argument is mutated, and no array
  stored in a value is handed out, so a value cannot change after it is
  built.

These laws are exercised by the tests in `src/core/core_test.mbt` and by every
capture-avoidance test of the higher packages.

## Alternatives rejected

- **De Bruijn indices everywhere.** Indices remove the need for names in the
  kernel, and the [debruijn package](debruijn.md) provides them, but
  downstream ASTs (polynomials, numeric expressions) are written and printed
  with names. Names stay the shared interface; indices are an internal
  representation chosen per algorithm.
- **Locally nameless or nominal types with name abstraction.** These need a
  richer type system or a library-wide change of representation, while the
  string-based design lets any downstream AST adopt the library by
  implementing one trait.
- **A global fresh-name counter.** Rejected as hidden state, see above.

## Boundaries

- `Name` has no scope, kind or sort. Distinguishing term variables from type
  variables, or variables of different downstream sorts, is left to the
  syntax that contains them.
- `Context` and `Telescope` do not check well-formedness: they neither reject
  duplicates nor check what annotations mention.
- `Renaming::equal` compares representations, not the denoted functions.
- `fresh_name` guarantees freshness only with respect to the set it is given.
  Supplying a complete set of used names is the caller's responsibility.
