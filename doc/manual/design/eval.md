# eval design

## Design goal

`eval` gives names to the reduction strategies that the literature and the
downstream packages talk about, and runs them on any rule through the
single-step machinery of [rewrite](rewrite.md). Choosing a strategy should be
a value that can be stored, compared and printed, not a different function
to call.

## Constraints

- **Strategies are data.** A strategy must be a value that can be stored,
  compared and printed.
- **No new semantics.** Every strategy is a traversal of [rewrite](rewrite.md),
  so it inherits the one-redex contract, the step-count contract and traces.

## Mathematical background

The strategies are defined for any rule $r$; the classical results are
stated for the beta rule of the lambda calculus,
$(\lambda x.\,b)\,a \to_\beta b[x := a]$, where `Apply` is read as a curried
spine and `Bind` as $\lambda$.

### Reduction contexts

A strategy is described by the contexts in which it may contract a redex,
together with an order among them. Writing $\Box$ for the hole:

$$
\begin{aligned}
\text{full:}\qquad C &::= \Box \;\mid\; \lambda x.\,C \;\mid\; C(\bar u) \;\mid\; t(u_0, \dots, C, \dots, u_n), \\
\text{weak head:}\qquad H &::= \Box \;\mid\; H(\bar u).
\end{aligned}
$$

- **Normal order** contracts the leftmost-outermost redex among all full
  contexts $C$.
- **Applicative order** contracts the leftmost-innermost redex among all
  full contexts $C$.
- **Weak head** reduction contracts the redex at the root if there is one,
  and otherwise looks only in the head position $H$; it never enters a
  binder or an argument.

A term on which weak head reduction finds no beta redex is in *weak head
normal form*: an abstraction $\lambda x.\,t$, or a spine
$h\,u_1 \cdots u_n$ whose head $h$ is a variable or a value.

The n-ary encoding adds one degenerate case, the empty spine
`Apply(h, [])`, whose curried reading is $h$ itself. The beta rule of
[utlc/lambda](utlc/lambda.md) reads it that way: it looks through empty
applications around the head, so `Apply(Apply(Bind(x, b), []), [a])` is the
redex $(\lambda x.\,b)\,a$ for every strategy. The node itself is not
removed, so the characterization above holds up to empty applications: a
weak head normal form is, after dropping them, an abstraction or a spine
with a variable or a value at its head.

### Classical results for beta

**Standardization and normalization.** If a term has a beta normal form,
normal order reduction reaches it.[^normal] Normal order is therefore a
*normalizing* strategy, which is why it is the default of the lambda calculus
packages.

[^normal]: Curry and Feys, *Combinatory Logic I*, 1958; see Barendregt, *The Lambda Calculus*, Theorem 13.2.2.

**Applicative order is not normalizing.** Let
$\Omega = (\lambda w.\,w\,w)(\lambda w.\,w\,w)$, which reduces only to itself.
For $t = (\lambda x.\,y)\,\Omega$:

$$
\begin{aligned}
\text{normal order:}\quad & (\lambda x.\,y)\,\Omega \;\to_\beta\; y && \text{root redex is outermost,}\\
\text{applicative order:}\quad & (\lambda x.\,y)\,\Omega \;\to_\beta\; (\lambda x.\,y)\,\Omega \;\to_\beta\; \cdots && \Omega \text{ is innermost.}
\end{aligned}
$$

**Agreement.** Beta reduction is confluent (Church–Rosser), so whenever two
strategies both reach a beta normal form, the normal forms are
alpha-equivalent.[^cr] A strategy can fail to terminate, but it cannot
produce a *different* normal form.

[^cr]: Church and Rosser, "Some properties of conversion", Transactions of the AMS 39, 1936.

**Weak head reduction** computes the weak head normal form when one exists;
it is the evaluation order of call-by-name languages and of the lazy
evaluator in [utlc/nbe](utlc/nbe.md).

## Design decisions

### Strategies as an enum

**Problem.** Callers need to select, record and compare strategies, for
example in a test that checks two strategies against each other.

**Options.** Pass a step function; pass a trait object; select from an enum.

**Choice.** `Strategy` is a plain enum with `Eq` and `Debug`, interpreted by
`reduce_once`. Custom strategies remain possible: any step function can be
given to `@rewrite.normalize` and `@rewrite.trace` directly. The enum covers
the named strategies only.

### Each strategy is one traversal of rewrite

$$
\begin{aligned}
\texttt{NormalOrder},\ \texttt{FullNormal} &\;\mapsto\; \texttt{top\_down\_once} && \text{(pre-order: leftmost-outermost)},\\
\texttt{ApplicativeOrder} &\;\mapsto\; \texttt{bottom\_up\_once} && \text{(post-order: leftmost-innermost)},\\
\texttt{WeakHead} &\;\mapsto\; \text{root, then head of } \texttt{Apply}, \text{ recursively}.
\end{aligned}
$$

Pre-order search returns the first redex that no other redex contains, scanning
head before arguments and arguments left to right; this is the
leftmost-outermost redex, and the normal-form lemma of the
[rewrite design](rewrite.md) shows that `NoStep` means "normal". Post-order
search returns a redex that contains no other redex, the leftmost-innermost
one. Weak head search follows only the spine, so its `NoStep` means "weak head
normal" and nothing more.

`evaluate` and `trace` add no reduction logic of their own: they pass the
strategy's step function to `@rewrite.normalize` and `@rewrite.trace`. As a
result, every strategy has a trace, and the step-count contract is the same
for all of them.

### `FullNormal` as a separate name

`FullNormal` maps to the same traversal as `NormalOrder` today. The
distinction is one of intent: `NormalOrder` promises the order of steps
(leftmost-outermost), `FullNormal` only promises a full normal form. Keeping
two names lets a faster full normalizer replace `FullNormal` later without
changing the meaning of `NormalOrder`.

## Correctness and invariants

- `reduce_once` satisfies the one-redex contract of
  [rewrite](rewrite.md) for every strategy; the reported path of a
  `WeakHead` step consists of `ApplyHead` frames only.
- For `NormalOrder`, `FullNormal` and `ApplicativeOrder`, `NoStep` means the
  rule applies nowhere; for `WeakHead`, nowhere on the head spine.
- With the beta rule, `evaluate(t, _, beta, NormalOrder, k)` returns
  `NormalForm` for every $t$ that has a beta normal form, provided $k$ is at
  least the length of the normal-order reduction (normalization theorem).
- If two strategies both return `NormalForm` for a confluent rule, the terms
  are alpha-equivalent (Church–Rosser).

The library's tests check named and De Bruijn beta steps against each other
(`src/utlc/lambda/lambda_test.mbt`), and normal order against the NbE
normalizer (`src/utlc/nbe/nbe_test.mbt`).

## Alternatives rejected

- **Call-by-value evaluation to values.** The usual call-by-value strategy
  does not reduce under binders and treats abstractions as values. It is
  expressible as a custom step function, but it is not one of the full or
  head strategies the packages need, so it is not in the enum.
- **Head reduction under binders.** Head reduction (reducing
  $\lambda \bar x.\,(\lambda y.\,b)\,a\,\bar u$ under the outer binders) can be
  written as a custom step function; the enum keeps to the strategies that
  are used.
- **Strategy-specific result types.** All strategies share
  `NormalizationResult`, so callers can switch strategies without changing
  their code.

## Boundaries

- Strategies only choose positions; they never rename, share or memoize.
  Repeated subterms are reduced separately.
- No call-by-value, call-by-need or head strategy is provided as a named
  case.
- Termination is bounded by `max_steps`, not decided.
- `eval` works on `Term[T]` only; downstream ASTs use
  `@rewrite.generic_normalize`, which is top-down.
