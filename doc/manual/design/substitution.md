# substitution design

## Design goal

Substitution is the operation every other part of the library is built on:
beta reduction substitutes an argument for a parameter, rewriting rules
instantiate their variables, and partial evaluation in downstream packages
replaces known variables by values. `substitution` provides one
capture-avoiding, simultaneous substitution for `Term[T]` and the same
algorithm for any `BindingSyntax` AST, with laws that hold up to
alpha-equivalence.

## Mathematical background

Terms, $\mathrm{FV}$, $\mathrm{names}$ and $=_\alpha$ are those of the
[syntax design](syntax.md).

### Substitutions

A *substitution* is a map $\sigma$ from names to terms that is the identity
$\sigma(x) = x$ outside a finite domain $\operatorname{dom}\sigma$. Its
*support* is
$\operatorname{supp}\sigma = \operatorname{dom}\sigma \cup \bigcup_{x \in \operatorname{dom}\sigma} \mathrm{names}(\sigma(x))$,
and $\sigma \setminus x$ removes $x$ from the domain. For a set of names $S$,
the *relevant range* of $\sigma$ on $S$ is

$$
R_\sigma(S) = \bigcup_{z \in S \cap \operatorname{dom}\sigma} \mathrm{FV}(\sigma(z)).
$$

### Capture-avoiding simultaneous substitution

`Substitution::apply` computes $t\sigma$ by

$$
\begin{aligned}
v\sigma &= v, \qquad x\sigma = \sigma(x), \qquad t(u_1, \dots, u_n)\sigma = (t\sigma)(u_1\sigma, \dots, u_n\sigma),\\
(\beta x.\, t)\sigma &=
\begin{cases}
\beta x.\; t\sigma' & \text{if } x \notin R_{\sigma'}(\mathrm{FV}(t)),\\[2pt]
\beta x'.\; \big(t\{x \mapsto x'\}\big)\sigma' & \text{otherwise,}
\end{cases}
\qquad \sigma' = \sigma \setminus x,
\end{aligned}
$$

where $x' = \operatorname{fresh}(x,\ \operatorname{supp}\sigma' \cup \mathrm{names}(t) \cup \{x\})$
and $t\{x \mapsto x'\}$ is the checked bound renaming of the syntax design.
The case split is exact: the binder is renamed only when a replacement that
is actually inserted into $t$ mentions $x$ free.

## Design decisions

### Simultaneous, one pass

**Problem.** Should $\{x \mapsto y,\ y \mapsto 2\}$ applied to $x + y$ give
$y + 2$ or $2 + 2$?

**Options.** Sequential substitution (apply the entries one after another),
iterated substitution (repeat until nothing changes), or simultaneous
substitution (every variable is looked up once in the original term).

**Choice.** Simultaneous. The variable case $x\sigma = \sigma(x)$ looks $x$
up once and never visits the inserted term again:

$$
\begin{aligned}
(x + y)\{x \mapsto y,\ y \mapsto 2\}
  &= x\{\dots\} + y\{\dots\} \\
  &= y + 2 .
\end{aligned}
$$

Simultaneous substitution is the one with an algebra (composition below), it
always terminates, and it expresses swaps such as $\{x \mapsto y,\ y \mapsto x\}$
directly. Sequential application is still available as composition with
`then`, and iteration to a fixed point is a policy of the caller. The
generic version is called `apply_once` to make this explicit.

### Rename binders only when needed

**Problem.** Capture happens when a binder $\beta x$ lies above an inserted
replacement in which $x$ is free. Renaming every binder avoids it but makes
results unreadable.

**Choice.** Rename only when $x \in R_{\sigma'}(\mathrm{FV}(t))$, and then
choose the fresh name with the hint $x$. The fresh name must avoid three
sets, each for its own reason:

- $\mathrm{FV}$ of the relevant replacements, or the renamed binder would
  capture them again;
- $\operatorname{dom}\sigma'$, or the occurrences that were renamed from
  $x$ to $x'$ would themselves be substituted (regression test "fresh
  binders avoid the substitution domain");
- $\mathrm{names}(t)$, so that the checked bound renaming
  $t\{x \mapsto x'\}$ cannot fail, and the renamed variable cannot be
  confused with an inner binder of the same name.

$\operatorname{supp}\sigma'$ covers the first two sets. The `abort` in the
implementation is therefore unreachable: by the freshness lemma
$x' \notin \mathrm{names}(t)$, which is exactly the side condition of
`alpha_rename_bound`.

### Composition as a first-class operation

`then` builds $\sigma \mathbin{;} \tau$ with

$$
(\sigma \mathbin{;} \tau)(x) =
\begin{cases}
\sigma(x)\,\tau & x \in \operatorname{dom}\sigma,\\
\tau(x) & x \in \operatorname{dom}\tau \setminus \operatorname{dom}\sigma,\\
x & \text{otherwise,}
\end{cases}
$$

so that sequential application can be expressed as one simultaneous
substitution, which is cheaper (one traversal) and has the laws below.

## Correctness / invariants

### Free variables

**Lemma 1.** $\mathrm{FV}(t\sigma) = \bigcup_{z \in \mathrm{FV}(t)} \mathrm{FV}(\sigma(z))$.

By induction on $t$. The variable, value and application cases are
immediate. For $\beta x.\,t$ without renaming, let $\sigma' = \sigma \setminus x$
and assume $x \notin R_{\sigma'}(\mathrm{FV}(t))$:

$$
\begin{aligned}
\mathrm{FV}\big((\beta x.\,t)\sigma\big)
  &= \mathrm{FV}(t\sigma') \setminus \{x\} \\
  &= \Big(\textstyle\bigcup_{z \in \mathrm{FV}(t)} \mathrm{FV}(\sigma'(z))\Big) \setminus \{x\} && \text{induction} \\
  &= \textstyle\bigcup_{z \in \mathrm{FV}(t),\, z \ne x} \mathrm{FV}(\sigma(z)) && (*) \\
  &= \textstyle\bigcup_{z \in \mathrm{FV}(\beta x.\,t)} \mathrm{FV}(\sigma(z)).
\end{aligned}
$$

Step $(*)$: for $z = x$, $\sigma'(x) = x$ contributes $\{x\}$, which is
removed. For $z \ne x$, $\sigma'(z) = \sigma(z)$, and $x \notin \mathrm{FV}(\sigma(z))$:
either $z \in \operatorname{dom}\sigma'$ and $\mathrm{FV}(\sigma(z)) \subseteq R_{\sigma'}(\mathrm{FV}(t)) \not\ni x$,
or $\sigma(z) = z \ne x$. With renaming, the same computation applies to
$x'$ and $t\{x \mapsto x'\}$, where $x' \notin \operatorname{supp}\sigma'$
makes the side condition hold. $\square$

**Corollary (no capture).** A variable free in an inserted replacement
$\sigma(z)$, $z \in \mathrm{FV}(t)$, is free in $t\sigma$.

### Only the free variables matter

**Lemma 2.** $t\sigma =_\alpha t\,(\sigma|_{\mathrm{FV}(t)})$, where
$\sigma|_S$ is `restrict(S)`.

The variable case is the definition. In the binder case, the renaming test
already restricts to $R_{\sigma'}(\mathrm{FV}(t))$, so both sides rename the
same binders, and only the variables in $\mathrm{FV}(t) \setminus \{x\}$ are
looked up. The fresh names may differ, because they avoid the support of
different substitutions, hence equality up to $=_\alpha$.

### Alpha-invariance

**Lemma 3.** If $t =_\alpha t'$ then $t\sigma =_\alpha t'\sigma$.

It suffices to check one alpha step $\beta x.\,t =_\alpha \beta y.\,t\{x \mapsto y\}$
with $y \notin \mathrm{names}(t)$. Both sides become binders over the same
body up to the bound name, and by Lemma 1 their bodies have the same free
variables outside the binder, so they are alpha-equivalent. As a consequence
substitution is well defined on alpha-equivalence classes, and the choice of
fresh names never matters semantically.

### Composition

**Lemma 4.** $t(\sigma \mathbin{;} \tau) =_\alpha (t\sigma)\tau$.

By Lemma 3 we may choose a representative of $t$ in which no binder lies in
$\operatorname{supp}\sigma \cup \operatorname{supp}\tau$; then no binder is
renamed on either side and both substitutions pass under binders unchanged.
The variable case splits as in the definition of $\sigma \mathbin{;} \tau$:

$$
\begin{aligned}
x \in \operatorname{dom}\sigma:&\quad x(\sigma;\tau) = \sigma(x)\tau = (x\sigma)\tau,\\
x \in \operatorname{dom}\tau \setminus \operatorname{dom}\sigma:&\quad x(\sigma;\tau) = \tau(x) = x\tau = (x\sigma)\tau,\\
\text{otherwise}:&\quad x(\sigma;\tau) = x = (x\sigma)\tau .
\end{aligned}
$$

The application and value cases follow by induction. $\square$

**Corollary (substitution lemma).** For $x \ne y$ and $x \notin \mathrm{FV}(r)$,

$$
t[x := s][y := r] \;=_\alpha\; t[y := r]\big[x := s[y := r]\big].
$$

Both sides are single simultaneous substitutions by Lemma 4. The left is
$\{x \mapsto s[y := r],\ y \mapsto r\}$. The right is
$\{y \mapsto r[x := s[y := r]],\ x \mapsto s[y := r]\}$, and
$r[x := \dots] = r$ because $x \notin \mathrm{FV}(r)$ (Lemma 1). The two maps
are equal, so the results are alpha-equivalent.[^substlemma] This is the
lemma that makes beta reduction compatible with substitution in the lambda
calculus packages.

[^substlemma]: Barendregt, *The Lambda Calculus*, Lemma 2.1.16.

### Renamings embed into substitutions

For a renaming $\rho$ and a list of names $L \supseteq \mathrm{FV}(t)$,
`from_renaming(L, ρ)` is $\sigma_\rho = \{x \mapsto \rho(x) \mid x \in L,\ \rho(x) \ne x\}$
(as variables), and $t\sigma_\rho =_\alpha t\rho$: both replace each free $x$
by the variable $\rho(x)$, and both freshen a binder exactly when it would
capture.

### Cost

Each binder computes the free variables of its body, so `apply` costs
$O(n \cdot d)$ hash-set operations for a term of size $n$ and binder depth
$d$, plus one extra body traversal per renamed binder. `then` costs one
`apply` per entry of `self`.

### Generic substitution

`GenericSubstitution::apply_once` is the same definition with every
constructor replaced by its `BindingSyntax` counterpart, so Lemmas 1–3 hold
for any implementation that satisfies the view laws of the
[adapter design](adapter.md). On `Term[T]` the two algorithms coincide.

## Alternatives rejected

- **The Barendregt variable convention.** Assuming that bound names are
  distinct from all free names would remove the renaming case, but terms come
  from users and from other algorithms, and the convention is not preserved
  by reduction. The library renames explicitly instead.
- **Substitution on De Bruijn terms only.** Index-based substitution needs no
  renaming and is provided by [debruijn](debruijn.md), but the shared
  interface for downstream ASTs is named, so named substitution must be
  correct on its own.
- **Iterated substitution.** Repeating until no domain variable occurs can
  diverge ($x \mapsto f(x)$) and has no composition law. Callers that want a
  fixed point iterate explicitly.

## Boundaries

- No unification, matching or occurs check: substitutions are given, not
  solved for.
- `GenericSubstitution` has no `then` or `restrict`; compose generic
  substitutions by applying them in turn.
- Results are equal to the textbook definition only up to $=_\alpha$; use
  `@syntax.alpha_equal` to compare them.
- Values are never entered, so a `Value` payload that contains variables is
  not substituted into.
