# substitution design

## Design goal

Substitution is the operation every other part of the library is built on:
beta reduction substitutes an argument for a parameter, rewriting rules
instantiate their variables, and partial evaluation in downstream packages
replaces known variables by values. `substitution` provides one
capture-avoiding, simultaneous substitution for `Term[T]` and the same
algorithm for any `BindingSyntax` AST, with laws that hold up to
alpha-equivalence.

## Constraints

- **Arbitrary input.** Terms come from users and from other algorithms, so
  substitution must be correct without assuming that bound and free names are
  distinct.
- **Determinism and readability.** Fresh names are reproducible and stay
  close to the original names; binders are renamed only when necessary.
- **One algorithm.** `Term[T]` and every `BindingSyntax` AST use the same
  definition, so one proof covers both.

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

## Correctness and invariants

`Substitution` and `GenericSubstitution` are abstract types: only the
functions of the package build them, each of those keeps at most one entry
per name, and `to_array` returns a copy of the entries. So every value
denotes a map $\sigma$ and keeps denoting the same map. The
replacement terms are shared, not copied; the laws assume, as the whole
library does, that terms are not changed in place.

The laws below are proved through the nameless reading of terms. The direct
argument by induction on named terms is the classical one, but its binder
case has to compare results whose fresh names differ, and that comparison is
exactly what the nameless reading makes trivial.

### The nameless reading

Let $\ulcorner t \urcorner$ be `@debruijn.from_named(t)`, the translation of
the [debruijn design](debruijn.md): bound occurrences become indices, free
names stay names. It is computed by *closing* each binder's variable. For a
nameless term $d$, let $\kappa^k_x\,d$ replace every free name $x$ under $j$
inner binders by the index $k + j$; then

$$
\ulcorner v \urcorner = v, \qquad
\ulcorner x \urcorner = x, \qquad
\ulcorner t(u_1, \dots, u_n) \urcorner = \ulcorner t \urcorner(\ulcorner u_1 \urcorner, \dots, \ulcorner u_n \urcorner), \qquad
\ulcorner \beta x.\, t \urcorner = \beta.\, \kappa^0_x \ulcorner t \urcorner .
$$

This is the same as the environment-based definition of `from_named`: the
occurrences of $x$ that are still free in $\ulcorner t \urcorner$ are exactly
those whose nearest binder is this one. Translations are *locally closed*:
every index points at a binder inside the term. Two facts are used below.

- **(T1)** $t =_\alpha u \iff \ulcorner t \urcorner = \ulcorner u \urcorner$
  (de Bruijn's theorem, see the [syntax design](syntax.md)).
- **(T2)** If $y \notin \mathrm{names}(t)$, then
  $\kappa^0_y \ulcorner t\{x \mapsto y\} \urcorner = \kappa^0_x \ulcorner t \urcorner$.
  The free name $y$ occurs in $\ulcorner t\{x \mapsto y\} \urcorner$ exactly
  where $x$ occurs free in $\ulcorner t \urcorner$, because $y$ occurs nowhere
  in $t$, so closing $y$ in the one gives the same indices as closing $x$ in
  the other.

On nameless terms, substitution for free names is plain replacement. For a
substitution $\sigma$ write $d\langle\sigma\rangle$ for $d$ with every free
name $z$ replaced by $\ulcorner \sigma(z) \urcorner$. No binder is renamed and
no index is shifted: the inserted terms are locally closed, so they mean the
same under any number of binders.

### The translation lemma

**Lemma 0.** $\ulcorner t\sigma \urcorner = \ulcorner t \urcorner\langle\sigma\rangle$
for every term $t$ and substitution $\sigma$.

By induction on the size of $t$, for all $\sigma$ at once. Values, variables
and applications are immediate. For $\beta x.\,t$ let
$\sigma' = \sigma \setminus x$. Closing commutes with replacement under two
conditions, checked occurrence by occurrence:

$$
\kappa^k_x\big(d\langle\sigma'\rangle\big) = \big(\kappa^k_x d\big)\langle\sigma'\rangle
\quad\text{if } x \notin \operatorname{dom}\sigma' \text{ and }
x \notin \mathrm{FV}(\sigma'(z)) \text{ for every free name } z \in \operatorname{dom}\sigma' \text{ of } d .
\tag{C}
$$

The first condition holds because $x$ was removed. The free names of
$\ulcorner t \urcorner$ are $\mathrm{FV}(t)$, so the second is exactly
$x \notin R_{\sigma'}(\mathrm{FV}(t))$. Hence, without renaming,

$$
\begin{aligned}
\ulcorner (\beta x.\,t)\sigma \urcorner
  &= \beta.\, \kappa^0_x \ulcorner t\sigma' \urcorner
   = \beta.\, \kappa^0_x \big(\ulcorner t \urcorner\langle\sigma'\rangle\big) && \text{induction} \\
  &= \beta.\, \big(\kappa^0_x \ulcorner t \urcorner\big)\langle\sigma'\rangle && \text{(C)} \\
  &= \beta.\, \big(\kappa^0_x \ulcorner t \urcorner\big)\langle\sigma\rangle
   = \ulcorner \beta x.\,t \urcorner\langle\sigma\rangle , && x \text{ is not free in } \kappa^0_x \ulcorner t \urcorner
\end{aligned}
$$

and with renaming to $x'$, which lies outside
$\operatorname{supp}\sigma' \cup \mathrm{names}(t)$,

$$
\begin{aligned}
\ulcorner (\beta x.\,t)\sigma \urcorner
  &= \beta.\, \kappa^0_{x'} \big(\ulcorner t\{x \mapsto x'\} \urcorner\langle\sigma'\rangle\big) && \text{induction, same size} \\
  &= \beta.\, \big(\kappa^0_{x'} \ulcorner t\{x \mapsto x'\} \urcorner\big)\langle\sigma'\rangle && \text{(C) for } x' \notin \operatorname{supp}\sigma' \\
  &= \beta.\, \big(\kappa^0_{x} \ulcorner t \urcorner\big)\langle\sigma'\rangle
   = \ulcorner \beta x.\,t \urcorner\langle\sigma\rangle . && \text{(T2)}
\end{aligned}
$$

$\square$

Everything else follows from Lemma 0, because replacement on locally closed
nameless terms is a homomorphism with no side conditions.

### Free variables

**Lemma 1.** $\mathrm{FV}(t\sigma) = \bigcup_{z \in \mathrm{FV}(t)} \mathrm{FV}(\sigma(z))$.

The free names of $\ulcorner t \urcorner\langle\sigma\rangle$ are those of the
inserted $\ulcorner \sigma(z) \urcorner$ for the free names $z$ of
$\ulcorner t \urcorner$, that is for $z \in \mathrm{FV}(t)$ (with
$\sigma(z) = z$ outside the domain). $\square$

**Corollary (no capture).** A variable free in an inserted replacement
$\sigma(z)$, $z \in \mathrm{FV}(t)$, is free in $t\sigma$.

### Only the free variables matter

**Lemma 2.** $t\sigma =_\alpha t\,(\sigma|_{\mathrm{FV}(t)})$, where
$\sigma|_S$ is `restrict(S)`. More generally, if $\sigma(z) =_\alpha \tau(z)$
for every $z \in \mathrm{FV}(t)$, then $t\sigma =_\alpha t\tau$.

$\ulcorner t \urcorner\langle\sigma\rangle$ consults $\sigma$ only at the free
names of $\ulcorner t \urcorner$, and only through
$\ulcorner \sigma(z) \urcorner$, which (T1) makes invariant under
$=_\alpha$. Equal translations mean alpha-equivalent terms by (T1). The two
sides need not be equal as values, because the fresh binder names avoid the
support of different substitutions. $\square$

### Alpha-invariance

**Lemma 3.** If $t =_\alpha t'$ then $t\sigma =_\alpha t'\sigma$.

By (T1), $\ulcorner t \urcorner = \ulcorner t' \urcorner$, so
$\ulcorner t\sigma \urcorner = \ulcorner t \urcorner\langle\sigma\rangle = \ulcorner t'\sigma \urcorner$
by Lemma 0, and (T1) again gives the claim. $\square$

Substitution is therefore well defined on alpha-equivalence classes, and the
choice of fresh names never matters semantically.

### Composition

**Lemma 4.** $t(\sigma \mathbin{;} \tau) =_\alpha (t\sigma)\tau$.

By Lemma 0 on both sides it suffices to show
$d\langle\sigma\rangle\langle\tau\rangle = d\langle\sigma \mathbin{;} \tau\rangle$
for a nameless $d$. Replacement is homomorphic, so only a free name $z$
needs checking, and it splits as in the definition of
$\sigma \mathbin{;} \tau$:

$$
\begin{aligned}
z \in \operatorname{dom}\sigma:&\quad z\langle\sigma\rangle\langle\tau\rangle = \ulcorner \sigma(z) \urcorner\langle\tau\rangle = \ulcorner \sigma(z)\,\tau \urcorner = z\langle\sigma \mathbin{;} \tau\rangle && \text{Lemma 0},\\
z \in \operatorname{dom}\tau \setminus \operatorname{dom}\sigma:&\quad z\langle\sigma\rangle\langle\tau\rangle = z\langle\tau\rangle = \ulcorner \tau(z) \urcorner = z\langle\sigma \mathbin{;} \tau\rangle,\\
\text{otherwise}:&\quad z\langle\sigma\rangle\langle\tau\rangle = z = z\langle\sigma \mathbin{;} \tau\rangle .
\end{aligned}
$$

$\square$

**Corollary (substitution lemma).** For $x \ne y$ and $x \notin \mathrm{FV}(r)$,

$$
t[x := s][y := r] \;=_\alpha\; t[y := r]\big[x := s[y := r]\big].
$$

By Lemma 4 each side is one simultaneous substitution applied to $t$. The
left is $\{x \mapsto s[y := r],\ y \mapsto r\}$. The right is
$\{y \mapsto r[x := s[y := r]],\ x \mapsto s[y := r]\}$, and
$r[x := s[y := r]] =_\alpha r$ by Lemma 2, because $x \notin \mathrm{FV}(r)$
and the empty substitution is the identity. The two substitutions agree up
to $=_\alpha$ at every name, so Lemma 2 makes the results
alpha-equivalent.[^substlemma] This is the lemma that makes beta reduction
commute with substitution in the lambda calculus packages:
$M \to_\beta N$ implies $M\sigma \to_\beta N\sigma$ up to $=_\alpha$.

[^substlemma]: Barendregt, *The Lambda Calculus*, Lemma 2.1.16.

### Renamings embed into substitutions

`Term::rename_free` obeys the analogue of Lemma 0,
$\ulcorner t\rho \urcorner = \ulcorner t \urcorner\langle\rho\rangle$, with the
same proof: its test $x \notin \operatorname{tgt}(\rho \setminus x)$ implies
the second condition of (C), and its fresh name avoids
$\operatorname{supp}(\rho \setminus x) \cup \mathrm{names}(t)$. For a list of
names $L \supseteq \mathrm{FV}(t)$, `from_renaming(L, ρ)` is
$\sigma_\rho = \{x \mapsto \rho(x) \mid x \in L,\ \rho(x) \ne x\}$ (as
variables). It agrees with $\rho$ on $\mathrm{FV}(t)$, so
$t\sigma_\rho =_\alpha t\rho$. The two results may still differ as values:
`rename_free` freshens a binder whenever it is a target of the renaming,
while `apply` freshens it only when an inserted variable would be captured.

### Cost

`apply` computes the free variables of every replacement once. At each
binder it removes one entry from the substitution and looks for entries
whose replacement has the binder free; only if there is one does it compute
the free variables of the body (see the capture test below). So a term of
size $n$ costs $O(n \cdot |\sigma|)$ besides the free variables of the
replacements, and each binder that is a candidate for capture adds one
traversal of its body, each renamed binder one more. `then` costs one
`apply` and one `set` per entry of `self`, so $O(k^2)$ entry copies for $k$
entries besides the applications.

### Generic substitution

`GenericSubstitution::apply_once` is the same definition with every
constructor replaced by its `BindingSyntax` counterpart. Reading a node
through its view gives a named term, so Lemmas 0–3 hold for any
implementation that satisfies the view laws of the
[adapter design](adapter.md). On `Term[T]` the two algorithms coincide.

### Traversal with an explicit work stack

**Problem.** The definition of $t\sigma$ is a structural recursion, and run
as host recursion it overflows the js, wasm and wasm-gc stacks on terms
nested a few thousand levels deep.

**Choice.** `Substitution::apply` and `GenericSubstitution::apply_once` are
one private loop, `substitute`, over the view of the generic substitution
above. It is an instance of the rebuild scheme of the
[syntax design](syntax.md) with the context $c = \sigma$ and

$$
\operatorname{binder}(x, t, \sigma) =
\begin{cases}
(x,\ t,\ \sigma') & \text{if } x \notin R_{\sigma'}(\mathrm{FV}(t)),\\
(x',\ t\{x \mapsto x'\},\ \sigma' \setminus x') & \text{otherwise,}
\end{cases}
$$

with $\sigma' = \sigma \setminus x$ and $x'$ as in the definition. By the
rebuild lemma the loop computes exactly $t\sigma$, the same term and the
same fresh names as the recursion, using a constant amount of host stack;
the analyses it calls ($\mathrm{FV}$, $\mathrm{names}$ and the checked bound
renaming) are stack-safe as well. On `Term[T]`, `Value` and the variables
outside the domain are returned as they are instead of being rebuilt, which
gives an equal term.

**The capture test.** The condition $x \in R_{\sigma'}(\mathrm{FV}(t))$ is
decided in a cheaper order. Unfolding $R$,

$$
x \in R_{\sigma'}(\mathrm{FV}(t))
\iff \exists z \in \operatorname{dom}\sigma'.\;
  x \in \mathrm{FV}(\sigma'(z)) \,\wedge\, z \in \mathrm{FV}(t)
\iff \exists z \in C.\; z \in \mathrm{FV}(t),
$$

where $C = \{z \in \operatorname{dom}\sigma' \mid x \in \mathrm{FV}(\sigma'(z))\}$
is the set of *candidates*. The sets $\mathrm{FV}(\sigma(z))$ are computed
once per call, and since $\sigma' \subseteq \sigma$ as a set of entries they
serve every binder. If $C = \varnothing$ the condition is false without
looking at $t$; otherwise $\mathrm{FV}(t)$ is computed once. The boolean is
the same, so the result is too, but a chain of $n$ binders none of which
can capture now costs $O(n)$ instead of $O(n^2)$.

The tests in `src/substitution/stack_safety_test.mbt` run substitution,
freshening at the outermost binder, deep replacements, composition and the
generic substitution on terms nested 100 000 levels deep, on every backend.

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
- Stack safety is in the nesting depth, not in the cost: a chain of $n$
  binders every one of which is renamed still costs $O(n^2)$, because each
  renaming traverses the body below it.
- Values are never entered, so a `Value` payload that contains variables is
  not substituted into.
