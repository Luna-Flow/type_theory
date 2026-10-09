# utlc/lambda design

## Design goal

`utlc/lambda` is the untyped lambda calculus written as directly as possible
on top of the shared layers: named terms from [syntax](../syntax.md),
capture-avoiding substitution from [substitution](../substitution.md), and a
strategy from [eval](../eval.md). It is meant to be obviously right rather
than fast, so that faster normalizers ([debruijn](../debruijn.md),
[utlc/nbe](nbe.md)) and the typed calculus [stlc](../stlc.md) can be checked
against it.

## Constraints

- **Obviously right.** The calculus is the reference that faster normalizers
  are tested against, so it reuses the shared substitution and strategies
  instead of reimplementing them.
- **Shared syntax.** Terms are `Term[T]`, so domain values ride along and
  every analysis of [syntax](../syntax.md) applies.

## Mathematical background

Lambda terms are $t ::= v \mid x \mid t\,u \mid \lambda x.\,t$, encoded as
`Value`, `Variable`, `Apply(t, [u])` and `Bind(x, t)`; an n-ary
`Apply(f, [a_1, …, a_n])` denotes the curried spine $f\,a_1 \cdots a_n$.
Terms are taken modulo $=_\alpha$.

### Beta and eta

$$
\begin{aligned}
(\beta)\quad & (\lambda x.\,b)\,a \;\to\; b[x := a], \\
(\eta)\quad & \lambda x.\,f\,x \;\to\; f \qquad \text{if } x \notin \mathrm{FV}(f).
\end{aligned}
$$

Both are closed under all contexts, including under $\lambda$ (the
$\xi$ rule). The side condition of eta is essential: without it
$\lambda x.\,x\,x \to x$ would turn a closed term into an open one and
identify functions that behave differently. Eta expresses *extensionality*:
in the presence of $\beta$, it is equivalent to the rule "if $f\,x = g\,x$ for
a fresh $x$ then $f = g$", because

$$
f \;\leftarrow_\eta\; \lambda x.\,f\,x \;=\; \lambda x.\,g\,x \;\to_\eta\; g
\qquad (x \notin \mathrm{FV}(f) \cup \mathrm{FV}(g)).
$$

### Classical properties

- **Confluence.** $\to_\beta$ and $\to_{\beta\eta}$ are Church–Rosser, so a
  term has at most one normal form up to $=_\alpha$.[^cr]
- **Normalization.** If a term has a beta normal form, the leftmost-outermost
  strategy reaches it (normalization theorem, see the [eval design](../eval.md)).
- **Eta postponement.** Every $\beta\eta$ reduction can be rearranged so that
  all $\beta$ steps precede all $\eta$ steps; consequently a term has a
  $\beta\eta$ normal form iff it has a $\beta$ normal form.[^postpone]
- **Undecidability.** Whether a term has a normal form is undecidable, which
  is why the normalizer takes a step limit.

[^cr]: Barendregt, *The Lambda Calculus*, Theorems 3.2.8 and 3.3.9.

[^postpone]: Barendregt, *The Lambda Calculus*, §15.1.

## Design decisions

### Beta through the shared substitution

`beta_rule` calls `Substitution::singleton(x, a).apply(b)`. All capture
avoidance is therefore in one place, proved once in the
[substitution design](../substitution.md). For the redex
$(\lambda x.\,\lambda y.\,x\,y)\,y$:

$$
\begin{aligned}
(\lambda x.\,\lambda y.\,x\,y)\,y
  &\to_\beta (\lambda y.\,x\,y)[x := y] \\
  &= \lambda y_1.\,(x\,y_1)[x := y] && y \in \mathrm{FV}(\text{replacement}),\ \text{rename } y \\
  &= \lambda y_1.\,y\,y_1 \\
  &\to_\eta y .
\end{aligned}
$$

Alpha-invariance of substitution (Lemma 3 of the substitution design) is
what makes beta well defined on alpha classes. The substitution lemma
(Barendregt 2.1.16, derived there as well) makes beta commute with
substitution, $M \to_\beta N \Rightarrow M\sigma \to_\beta N\sigma$, which
the confluence proofs rely on.

### Spines are contracted one argument at a time

A redex is `Apply(Bind(x, b), [a, ..rest])`. It contracts with the first
argument only and keeps the rest:
$(\lambda x.\,b)\,a\,\bar r \to b[x := a]\,\bar r$. This is beta on the
curried reading of the spine, so every step is a single beta step and the
step count equals the length of the corresponding curried reduction. The De
Bruijn reducer makes the same choice, which keeps the two step by step
comparable.

### Eta only on unary applications

`eta_rule` matches `Bind(x, Apply(f, [Variable(x)]))`. On the curried
reading, $\lambda x.\,f\,a\,x$ (written `Apply(f, [a, x])`) is also an eta
redex, but recognising it would require splitting the spine and rebuilding
`Apply(f, [a])`. The rule stays syntactic; callers who build spines n-ary and
need eta can normalize spines to unary form first.

### Normal order with one combined rule

`normalize` runs `beta_eta_rule` with the `NormalOrder` strategy, so each step
contracts the leftmost-outermost redex of either kind. The combined rule has
one name, `"beta_eta"`; traces show positions but not which of the two rules
fired. Because beta and eta redexes have different root constructors, the
priority inside `beta_eta_rule` never changes the outcome of a step.

### Beta then eta versus `normalize`

**Problem.** A caller may compute the beta normal form $N$ first, with
`@eval.evaluate(t, _, beta_rule, NormalOrder, _)`, and then its eta normal
form $M$, with `eta_rule`. Does $M$ agree with the result $L$ of
`normalize(t, _)`?

**Not literally.** The rules read `Apply(h, [])` as $h$ when they match a
redex, but no rule removes the node. On
$t = \lambda z.\,(\lambda y.\,y)\,(z\,())$, where $z\,()$ is
`Apply(Variable(z), [])`, beta alone gives $N = \lambda z.\,z\,()$, and
$\lambda z.\,z\,()$ is no eta redex because its body is not an application
to $z$; so $M = N$. `normalize` instead contracts the eta redex at the root
first, reading the argument $z\,()$ as $z$, and returns
$L = \lambda y.\,y$. $M$ and $L$ are not alpha-equivalent.

**Agreement modulo empty applications.** Let $\lfloor \cdot \rfloor$ erase
every empty application:

$$
\begin{aligned}
\lfloor v \rfloor &= v, &
\lfloor x \rfloor &= x, &
\lfloor \lambda x.\,t \rfloor &= \lambda x.\,\lfloor t \rfloor, \\
\lfloor \texttt{Apply}(h, []) \rfloor &= \lfloor h \rfloor, &
\lfloor \texttt{Apply}(h, [a_1, \dots, a_n]) \rfloor &= \texttt{Apply}(\lfloor h \rfloor, [\lfloor a_1 \rfloor, \dots, \lfloor a_n \rfloor]) \quad (n \ge 1).
\end{aligned}
$$

Call a term *unary* when each of its `Apply` nodes has at most one argument;
terms built with `application` are unary. On a unary term,
$\lfloor \cdot \rfloor$ gives an ordinary lambda term with binary
application.

**Theorem.** Let $t$ be unary. If
`@eval.evaluate(t, _, beta_rule, NormalOrder, _)` returns `NormalForm(N, _)`,
`@eval.evaluate(N, _, eta_rule, NormalOrder, _)` returns `NormalForm(M, _)`,
and `normalize(t, _)` returns `NormalForm(L, _)`, then
$\lfloor M \rfloor =_\alpha \lfloor L \rfloor$.

*Proof.* (1) *Unary terms are closed under the rules.* Beta on a unary
redex `Apply(h, [a])` returns $b[x := a]$ with no remaining spine;
substitution copies the unary term $a$ into the unary term $b$; eta returns
a subterm. (2) *Erasure is a step-by-step simulation on unary terms.*
Erasure keeps every name, so it commutes with capture-avoiding substitution
up to $=_\alpha$:
$\lfloor b[x := a] \rfloor =_\alpha \lfloor b \rfloor[x := \lfloor a \rfloor]$.
`beta_rule` fires on `Apply(h, [a])` exactly when $h$ is a `Bind` wrapped in
empty applications, that is, when
$\lfloor \texttt{Apply}(h, [a]) \rfloor = (\lambda x.\,\lfloor b \rfloor)\,\lfloor a \rfloor$
is a beta redex, and the contractum erases to its contractum. `eta_rule`
fires on `Bind(x, B)` exactly when $B$ is `Apply(f, [a])` up to empty
applications with $a$ a wrapped `Variable(x)` and $x \notin \mathrm{FV}(f)$,
that is, when $\lambda x.\,\lfloor B \rfloor = \lambda x.\,\lfloor f \rfloor\,x$
is an eta redex. No rule fires on an empty application itself, and the
redexes of $\lfloor u \rfloor$ are the images of the redexes of $u$, where an
empty application contributes the redexes of its head. Hence a rule step
$u \to u'$ is a step $\lfloor u \rfloor \to \lfloor u' \rfloor$ of the same
kind up to $=_\alpha$, and a term with no redex for the rules erases to a
term with no redex.
(3) By (2), $\lfloor t \rfloor \to_\beta^{*} \lfloor N \rfloor$ with
$\lfloor N \rfloor$ beta-normal, then
$\lfloor N \rfloor \to_\eta^{*} \lfloor M \rfloor$ with $\lfloor M \rfloor$
eta-normal. Eta steps keep a term beta-normal: a new beta redex would need
$(\lambda x.\,f\,x)\,a$ or $\lambda x.\,(\lambda y.\,b)\,x$ in the term,
both beta redexes already. So $\lfloor M \rfloor$ is beta-eta normal and
$\lfloor t \rfloor \to_{\beta\eta}^{*} \lfloor M \rfloor$. Likewise
$\lfloor t \rfloor \to_{\beta\eta}^{*} \lfloor L \rfloor$ with
$\lfloor L \rfloor$ beta-eta normal. By confluence of $\to_{\beta\eta}$ the
two normal forms are alpha-equivalent. $\square$

On the example, $\lfloor M \rfloor = \lambda z.\,z$ and
$\lfloor L \rfloor = \lambda y.\,y$. Equivalently, $M$ and $L$ are equal in
the least congruence containing $=_\alpha$ and `Apply(h, [])` $= h$; in
particular their nameless, spine-flattened forms are equal.

The unary hypothesis is needed for eta only. On the curried reading,
`Bind(x, Apply(f, [a, Variable(x)]))` is the eta redex
$\lambda x.\,(f\,a)\,x$, which `eta_rule` does not recognise (see "Eta
only on unary applications" above), so for terms with longer spines step (2)
fails and no agreement is claimed.

## Correctness and invariants

- `beta_rule(t) = Some(u)` implies $t \to_\beta u$ at the root; `eta_rule`
  likewise for $\eta$, with the side condition checked by
  `@syntax.free_variables`.
- `normalize` returns `NormalForm(u, n)` only for $u$ with no (unary)
  $\beta$ or $\eta$ redex anywhere ([rewrite](../rewrite.md) normal-form
  lemma).
- By confluence of beta, the beta normal forms computed by
  `@eval.evaluate` with `beta_rule`, by [debruijn](../debruijn.md) and by
  [utlc/nbe](nbe.md) coincide after conversion and spine flattening. The test
  "named and debruijn beta reduction agree modulo alpha" checks a step that
  requires renaming.
- `normalize` returns a beta-eta normal form, which is in general *not* the
  beta normal form of the other normalizers: $\lambda x.\,f\,x$ is beta-normal
  and normalizes to $f$ here. The two are related by eta alone, but only
  modulo empty applications and for unary spines, as the theorem in "Beta
  then eta versus `normalize`" above states.
- With beta and eta combined, normal order is used as the strategy; that it
  reaches the $\beta\eta$ normal form of every normalizing term rests on the
  normalization theorem for beta and eta postponement, and is checked by tests
  rather than proved here.

## Alternatives rejected

- **A separate lambda AST.** Using `Term[T]` keeps the calculus inside the
  shared substrate: the same analyses, substitution and traces apply, and
  domain values ride along unchanged.
- **Separate beta and eta normalizers.** Offered indirectly: pass
  `beta_rule` or `eta_rule` to [`@eval.evaluate`](../../api/eval.md) with any
  strategy.
- **Iterated substitution in beta.** Beta substitutes once; the argument is
  not re-substituted, as the calculus requires.

## Boundaries

- No types: ill-behaved terms such as $\Omega$ are accepted and end with
  `StepLimitReached`.
- No sharing: a duplicated argument is reduced once per copy. Use
  [utlc/nbe](nbe.md) for efficient normalization.
- Eta recognises unary applications only.
- An empty application `Apply(h, [])` is read as $h$ when a redex is
  matched, but it is not removed from the term (see the
  [eval design](../eval.md)). Results of different reduction orders, such
  as beta then eta and `normalize`, therefore agree only after empty
  applications are erased.
- Constants (`Value`) have no reduction rules here; add domain rules with
  [rewrite](../rewrite.md) or [eval](../eval.md).
