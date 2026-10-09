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
- **No new semantics.** Every strategy is a single-step function in the
  sense of [rewrite](rewrite.md): it rewrites one position of the term with
  the rule, so it inherits the one-redex contract, the step-count contract
  and traces.
- **One meaning per term.** An n-ary spine `Apply(f, [a1, a2])` and the
  nested `Apply(Apply(f, [a1]), [a2])` both denote $f\,a_1\,a_2$; a named
  strategy must take the same steps on both.

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

"Leftmost", "outermost" and "innermost" refer to the curried reading of the
term, in which $t(u_1, \dots, u_n)$ stands for
$(\cdots((t\,u_1)\,u_2)\cdots)\,u_n$ and the partial applications
$t\,u_1 \cdots u_i$ are subterms as well. For beta this matters: in
$(\lambda x.\,b)\,a_1\,a_2$ the redex is the prefix
$(\lambda x.\,b)\,a_1$, which does not contain $a_2$, so applicative order
contracts it before any redex inside $a_2$.

### Curried prefixes and n-ary positions

A prefix $t\,u_1 \cdots u_i$ with $i < n$ is not a position of the n-ary
tree, so a step cannot be reported there. The beta rule does not need one:
it contracts a spine with its first argument and keeps the rest, so that
for $n \ge 2$

$$
\beta\big(t(u_1, \dots, u_n)\big) = \beta\big(t(u_1)\big)(u_2, \dots, u_n),
$$

and the left side is defined exactly when the right side is. A beta step at
the prefix $t\,u_1$ is therefore the step at the whole spine, reported at the
spine's position. The strategies use this in one direction only: a prefix
decides *when* the whole application is tried, never *what* is rewritten.

- Normal order and weak head try the whole application before its head and
  arguments. The prefixes lie between the two, and a beta redex at a prefix
  is a redex at the whole application, so the n-ary order already agrees
  with the curried one.
- Applicative order tries the head, then the arguments from left to right.
  After argument $u_i$ with $i < n$, it tries the rule on the whole
  application if the rule applies to the prefix $t(u_1, \dots, u_i)$, and
  after $u_n$ in any case. For beta this is post-order on the curried
  reading.

A rule that matches applications of one arity only, such as
`Apply(Value("+"), [Value("0"), x])`, never applies to a shorter prefix, so
for it applicative order is post-order on the n-ary tree. A rule that
applies to a prefix but not to the whole application rewrites nothing
there: the prefix is not a position.

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

### Each strategy is one traversal

$$
\begin{aligned}
\texttt{NormalOrder},\ \texttt{FullNormal} &\;\mapsto\; \texttt{top\_down\_once} && \text{(pre-order: leftmost-outermost)},\\
\texttt{ApplicativeOrder} &\;\mapsto\; \text{post-order on curried spines} && \text{(leftmost-innermost)},\\
\texttt{WeakHead} &\;\mapsto\; \text{root, then head of } \texttt{Apply}, \text{ recursively}.
\end{aligned}
$$

Pre-order search returns the first redex that no other redex contains, scanning
head before arguments and arguments left to right; this is the
leftmost-outermost redex, and the normal-form lemma of the
[rewrite design](rewrite.md) shows that `NoStep` means "normal". Post-order
search on the curried reading returns, for beta and for rules of one arity, a
redex that contains no other redex, the leftmost-innermost one; it tries the
rule at every position, so its `NoStep` also means "normal". Weak head search follows only the spine, so its
`NoStep` means "weak head normal" and nothing more.

### Applicative order reads spines curried

**Problem.** `@rewrite.bottom_up_once` is post-order on the n-ary tree: it
tries every argument of `Apply(h, [a1, …, an])` before the application. For
beta it reduces inside $a_2$ before the redex $(\lambda x.\,b)\,a_1$, while
the nested encoding contracts that redex first. The normal form is the same,
but the steps, paths and traces depend on how the term was built.

**Options.** Keep `bottom_up_once` and document the dependence; rewrite the
prefix `Apply(h, [a1, …, ai])` on its own; let the prefix only decide when
the whole application is tried.

**Choice.** The last. Rewriting a prefix would report a step at a position
that does not exist, against the path contract of
[rewrite](rewrite.md). Trying the whole application early keeps every step
a rule application at a real position, and for beta it yields exactly the
curried order (previous section). The traversal lives in `eval`, next to
the weak head one; `@rewrite.bottom_up_once` stays post-order on the n-ary
tree, because for the symbolic ASTs that `rewrite` serves, an n-ary
operator application is one node, not a curried spine. The cost is one
extra rule attempt per argument of a spine, on a prefix built for the
attempt.

`evaluate` and `trace` add no reduction logic of their own: they pass the
strategy's step function to `@rewrite.normalize` and `@rewrite.trace`. As a
result, every strategy has a trace, and the step-count contract is the same
for all of them.

### Searches with a bounded host stack

**Problem.** Like the traversals of [rewrite](rewrite.md), the weak head and
applicative searches were structural recursion, so a redex nested a few
thousand levels deep overflowed the js, wasm and wasm-gc stacks (issue #13).

**Choice.** Both run as loops over the stack of ancestors described in "A
bounded host stack" of the [rewrite design](rewrite.md): a heap array of parent
nodes with the edge taken from each, root first, rebuilt from the innermost
outwards when a step is found. `NormalOrder` and `FullNormal` use
`@rewrite.top_down_once` itself.

- *Weak head.* The search tries $r$ at the root and, while it fails at an
  application, descends into the head. The ancestors are all
  `ApplyHead` entries; the loop tries the same nodes in the same order and
  rebuilds $h'\,\vec u_k \cdots \vec u_1$ around the result $h'$, which is
  what the recursion returned.
- *Applicative order.* The search is the post-order search of
  [rewrite](rewrite.md), with one change where an
  argument has been searched without a step: leaving argument $i$ of
  $s = h\,a_0 \cdots a_{n-1}$ with $i < n - 1$ first tries the prefix
  $h\,a_0 \cdots a_i$ and, if the prefix is a redex, the whole $s$, exactly
  as the recursive loop over the arguments does after each argument. The
  recursion keeps one local variable across that loop, `root_failed`
  (the early attempt at $s$ failed, so $s$ is not tried again after the last
  argument). The ancestor entry for argument $i$ carries it,
  $(s, \mathsf{A}_i, \mathit{failed})$, and passes it on to the entry for
  argument $i + 1$, so every attempt, at a node or at a prefix, happens in
  the order and with the outcome of the recursive definition.

Steps, paths and traces are therefore unchanged; the host stack depth is
constant, and the heap holds one entry per level of the current position.

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
- With the beta rule, every strategy takes the same steps on a term and on
  its curried form, in which every `Apply(f, [a1, …, an])` with $n > 0$ is
  nested into unary applications: after each step the two terms are again a
  term and its curried form, up to alpha-equivalence.
- For `NormalOrder`, `FullNormal` and `ApplicativeOrder`, `NoStep` means the
  rule applies nowhere; for `WeakHead`, nowhere on the head spine.
- With the beta rule, `evaluate(t, _, beta, NormalOrder, k)` returns
  `NormalForm` for every $t$ that has a beta normal form, provided $k$ is at
  least the length of the normal-order reduction (normalization theorem).
- If two strategies both return `NormalForm` for a confluent rule, the terms
  are alpha-equivalent (Church–Rosser).
- Every strategy uses a constant host stack depth; a redex nested 100 000
  levels deep is found and rewritten on every backend
  (`src/eval/deep_test.mbt`).

The library's tests check named and De Bruijn beta steps against each other
and every strategy on random terms against their curried forms
(`src/utlc/lambda/lambda_test.mbt`), applicative order with rules of fixed
arity (`src/eval/eval_test.mbt`), and normal order against the NbE
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
