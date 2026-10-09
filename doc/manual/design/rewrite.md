# rewrite design

## Design goal

`rewrite` turns a *local* rule, a partial function that rewrites a term at
its root, into *global*, auditable reduction: one step at a chosen position,
with a record of where and by which rule, and bounded repetition of such
steps. All operational semantics of the library (the [eval](eval.md)
strategies, the [lambda](utlc/lambda.md) calculus, the De Bruijn reducer of
[debruijn](debruijn.md)) are defined as single-step functions of this shape,
so that every normalizer can be explained step by step.

## Constraints

- **Auditability.** Every step must be observable: the term before and
  after, the rule and the position.
- **Arbitrary rules.** A rule is any MoonBit function, so termination and
  confluence cannot be decided; repetition must be bounded.
- **Immutable terms.** Steps build new terms and never update in place.
  Unchanged subterms are shared between `before` and `after`, so callers
  must not change the argument array of an `Apply` node either.

## Mathematical background

### Abstract rewriting systems

An *abstract rewriting system* is a set $A$ with a relation
$\to\ \subseteq A \times A$.[^terese] Write $\to^{*}$ for its reflexive
transitive closure and $\leftrightarrow^{*}$ for its equivalence closure.

- $a$ is a *normal form* if there is no $b$ with $a \to b$.
- $\to$ is *terminating* (strongly normalizing) if there is no infinite chain
  $a_0 \to a_1 \to \cdots$, and *weakly normalizing* if every element reduces
  to some normal form.
- $\to$ is *confluent* if $b \leftarrow^{*} a \to^{*} c$ implies
  $b \to^{*} d \leftarrow^{*} c$ for some $d$, and *locally confluent* if this
  holds for one-step forks $b \leftarrow a \to c$.

Confluence makes normal forms unique: if $a \to^{*} n_1$ and $a \to^{*} n_2$
with both normal, a common reduct $d$ must equal both. Newman's lemma states
that a terminating, locally confluent system is confluent; local confluence of
a term rewriting system follows from the joinability of its critical pairs
(Knuth–Bendix).[^newman]

[^terese]: Terese, *Term Rewriting Systems*, Cambridge University Press 2003, chapter 1.

[^newman]: M. H. A. Newman, "On theories with a combinatorial definition of equivalence", Annals of Mathematics 43, 1942.

### Positions and contexts

A *position* is a path $p$ of frames from the root: `BinderBody` enters
$\beta x.\,\Box$, `ApplyHead` enters $\Box(\bar u)$, `ApplyArgument(i)`
enters the $i$-th argument. Write $t|_p$ for the subterm at $p$ and
$t[s]_p$ for $t$ with that subterm replaced by $s$:

$$
\begin{aligned}
t|_{\varepsilon} &= t, &
(\beta x.\,t)|_{\mathsf{B}\cdot p} &= t|_p, &
t(\bar u)|_{\mathsf{H}\cdot p} &= t|_p, &
t(u_0,\dots,u_n)|_{\mathsf{A}_i\cdot p} &= u_i|_p .
\end{aligned}
$$

### The rewrite relation of a rule

A rule is a partial function $r : \mathrm{Term} \rightharpoonup \mathrm{Term}$.
A *redex* of $r$ is a term in its domain. The rewrite relation of $r$ is its
closure under contexts:

$$
\frac{t|_p \in \operatorname{dom} r}{t \;\to_r\; t[\,r(t|_p)\,]_p}
$$

A *strategy* is a partial function $S$ with $S(t) \in \{\, u \mid t \to_r u \,\}$
whenever it is defined; it chooses one of the possible steps. The traversal
functions of this package are strategies, and `StepResult` makes the choice
observable.

## Design decisions

### The single step is the primitive

**Problem.** A normalizer that rewrites "everything it can" in one pass is
fast, but its behaviour cannot be compared with a specification, and its
intermediate states are lost.

**Choice.** The primitive is one step at one position, returned as
`Reduced(before, after, rule, path)` or `NoStep`. Its contract, checked by
construction in the implementation, is

$$
\texttt{Reduced}(t, u, r, p) \implies t|_p \in \operatorname{dom} r \;\wedge\; u = t[\,r(t|_p)\,]_p ,
$$

so each reported step is a step of $\to_r$ at exactly the reported position.
The traversals build `after` by rebuilding only the nodes on the path, and
build `path` by prepending one frame per level on the way back up. Normalizers
and traces are loops over this primitive and add nothing semantic. The cost of
the design is that a full normalization repeats a traversal from the root for
every step; the benefit is that every normalizer has a trace, and that two
implementations can be compared step by step.

### Strategies as traversal orders

`top_down_once` tries the rule at a node before its children, children in the
order head, argument 0, argument 1, … It returns the first redex in
pre-order, which is the *leftmost-outermost* redex: no redex contains it, and
among such redexes it is the leftmost. `bottom_up_once` tries children first
and returns the first redex in post-order, the *leftmost-innermost* redex: it
contains no other redex.

"Contains" refers to positions of the n-ary tree, where
`Apply(h, [a1, …, an])` is one node above all of its arguments. This is the
reading of the symbolic ASTs the package serves, where an operator applied to
several arguments is one node. The lambda calculus reads the node as the
curried spine $h\,a_1 \cdots a_n$, in which a beta redex
$(\lambda x.\,b)\,a_1$ is a prefix that does not contain $a_2$; there,
`bottom_up_once` reduces inside $a_2$ before that redex, and the nested
encoding does not. The `ApplicativeOrder` strategy of [eval](eval.md)
therefore uses its own traversal, which follows the curried reading and still
rewrites only positions of the n-ary tree.

**Lemma (normal forms).** For both traversals, `NoStep` on $t$ iff $t$ is a
normal form of $\to_r$.

Both traversals visit every position of $t$ (they enter binder bodies, the
head and all arguments) and try $r$ there. They return `NoStep` only after
every attempt returned `None`, so no position is a redex; conversely, if some
position is a redex, the traversal reaches it unless it returns earlier with
another step. $\square$

Hence `normalize` with either traversal returns `NormalForm(t, n)` only when
$t$ is $\to_r$-normal. Other strategies, such as weak-head reduction in
[eval](eval.md), visit fewer positions; for them `NoStep` only means "no
redex at a position the strategy considers".

### Bounded repetition with an exact count

`normalize(t, step, k)` computes the sequence $t_0 = t$,
$t_{i+1} = \mathit{after}(\mathit{step}(t_i))$ and stops at the first $n$
with $\mathit{step}(t_n) = \texttt{NoStep}$ or at $n = k$:

$$
\texttt{normalize}(t, \mathit{step}, k) =
\begin{cases}
\texttt{NormalForm}(t_n, n) & n \le k,\ \mathit{step}(t_n) = \texttt{NoStep},\\
\texttt{StepLimitReached}(t_k, k) & \mathit{step}(t_k) \ne \texttt{NoStep}.
\end{cases}
$$

The extra call at $n = k$ distinguishes "normal after exactly $k$ steps" from
"limit reached", so the result never claims a normal form that it has not
checked. A limit $k \le 0$ behaves like $k = 0$: no step is taken and $t$ is
only classified. A step limit is necessary because termination is not decidable for
arbitrary rules (and fails for the untyped lambda calculus); it is a
parameter, not a global setting.

### Rules are named, not registered

**Problem.** Rewriting systems usually have several rules.

**Options.** A rule registry inside the package; a list of rules per call; one
rule function per call.

**Choice.** One rule function with one `RuleName` per call. A system with
several rules is either combined into one rule (as `beta_eta_rule` in
[lambda](utlc/lambda.md), which tries beta before eta at each position), or
expressed as a step function that tries several single-rule traversals in
turn. The two choices give different strategies: the first picks the
outermost position at which *any* rule applies, the second prefers the first
rule anywhere in the term. Keeping that choice with the caller avoids fixing
one priority scheme for every language.

### Generic traversal through the view

`generic_top_down_once` is `top_down_once` with `project` for pattern
matching and the trait constructors for rebuilding. It needs no knowledge of
the downstream AST beyond the [view laws](adapter.md), so a polynomial or
numeric-expression AST gets positions and traces for free. Only the top-down
strategy is provided generically, because it is the one downstream
simplifiers use and because it makes the normal-form lemma available.

## Correctness and invariants

- One step rewrites at most one position, and the reported `path` addresses
  it in `before` (contract above). Tested by "structured step records rule and
  root path" and the path tests of [debruijn](debruijn.md).
- `NoStep` from `top_down_once`, `bottom_up_once` or `generic_top_down_once`
  means the term is normal for the rule (normal-form lemma).
- `normalize` and `trace` perform at most `max_steps` steps and call `step`
  at most `max_steps + 1` times; `NormalForm(t, n)` implies `step(t) = NoStep`.
- In a `ReductionTrace` the final term of `result` is the last `after` (or
  `initial` when there are no steps), and the number of recorded steps is the
  count in `result`. If the step function reports its input as `before`, as
  every traversal of this package and of [eval](eval.md) does, then also
  `steps[0].before = initial` and `steps[i].after = steps[i+1].before`.
  `trace` records what the step function returns and does not check this.
- `ReductionPath` and `ReductionTrace` are abstract and their accessors
  return copies of the stored arrays, so a path or a trace cannot change
  after it is built and the laws above, once true of it, stay true.

**What is not checked.** The package does not decide termination or
confluence of a rule. When the rule is confluent, every terminating strategy
reaches the same normal form; when it is not, different strategies can
legitimately return different normal forms, and the trace shows why.

Cost: one step costs $O(n)$ rule attempts for a term of size $n$, plus
rebuilding the path; normalizing in $k$ steps costs $O(k \cdot n)$ rule
attempts.

## Alternatives rejected

- **In-place or memoized rewriting.** Faster, but loses `before` and the
  path, and conflicts with immutable terms.
- **A fixed rule language (patterns with variables).** A pattern language
  would need matching and an occurs check; a rule as a MoonBit function can
  use pattern matching of the host language and any side condition.
- **Capture-aware traversal.** The traversal could rename binders before
  passing an open subterm to a rule. Rules that need binding-aware behaviour
  use [substitution](substitution.md), which already renames; renaming in the
  traversal would change binder names behind the rule's back.

## Boundaries

- Rules see subterms under binders as open terms; the traversal neither
  renames nor reports which binders are in scope. A rule must be correct on
  open terms.
- No matching modulo associativity, commutativity or alpha-equivalence; a
  rule matches with MoonBit patterns on the term as it is.
- No termination, confluence or critical-pair analysis.
- Generic versions exist only for the top-down strategy and for
  normalization without a trace.
- The bound `max_steps` counts steps, not time or memory.
