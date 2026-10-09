# debruijn design

## Design goal

Named syntax needs fresh names and renaming in every binder-crossing
operation. `debruijn` provides a representation in which alpha-equivalence is
syntactic equality and beta reduction needs no renaming at all, together with
exact translations to and from named syntax. It is the kernel representation
of the untyped NbE in [utlc/nbe](utlc/nbe.md) and a reference reducer against
which the named calculus in [utlc/lambda](utlc/lambda.md) is tested.

## Constraints

- **Exact translations.** Converting to indices and back must lose nothing
  but binder names.
- **Errors are values.** An ill-scoped index is reported as a `ScopeError`,
  never by an abort or a silently wrong term where the operation can detect it.
- **Open terms.** Free variables come from users and downstream ASTs, so they
  stay names instead of needing a global numbering.

## Mathematical background

### Indices

In a term with nameless binders, a bound occurrence is a number $i$, its
*De Bruijn index*: the number of binders between the occurrence and the
binder it refers to.[^db] With $\lambda$ for `Bind` and juxtaposition for
`Apply`:

$$
\lambda x.\,\lambda y.\,x\,y \;\rightsquigarrow\; \lambda.\,\lambda.\,1\;0 ,
\qquad
\lambda x.\,x\,(\lambda y.\,x\,y) \;\rightsquigarrow\; \lambda.\,0\,(\lambda.\,1\,0).
$$

The same variable has different indices at different depths (here $x$ is $0$
and then $1$). Free variables stay named (`Free(x)`), a "locally nameless"
choice for the free part that keeps translations simple.

A term is *well scoped at depth $n$* when every index under $k$ binders is
smaller than $n + k$; it is well scoped when it is well scoped at depth $0$.
`validate` decides this.

[^db]: N. G. de Bruijn, "Lambda calculus notation with nameless dummies", Indagationes Mathematicae 34, 1972.

### Levels

The *level* of a binder is its depth counted from the root. An occurrence
under $n$ binders with index $i$ refers to the binder at level

$$
\ell = n - 1 - i, \qquad\text{equivalently}\qquad i = n - 1 - \ell .
$$

When a term is moved under one more binder (weakening: the context grows at
its inner end), the indices of its free variables must be shifted by one, but
their levels do not change. The NbE evaluator therefore uses levels for the
variables it invents while going under binders, so that semantic values can
be moved deeper without shifting, and converts back with $i = n - 1 - \ell$
when quoting.

### Shifting

$\uparrow^{d}_{c}\,t$ adds $d$ to every index of $t$ that is free relative to
cutoff $c \ge 0$:

$$
\begin{aligned}
\uparrow^{d}_{c}\,i &= \begin{cases} i & i < c \\ i + d & i \ge c \end{cases}, &
\uparrow^{d}_{c}\,(\lambda.\,t) &= \lambda.\,\uparrow^{d}_{c+1} t, \\
\uparrow^{d}_{c}\,(t\,\bar u) &= (\uparrow^{d}_{c} t)\,(\overline{\uparrow^{d}_{c} u}), &
\uparrow^{d}_{c}\,v &= v, \quad \uparrow^{d}_{c}\,x = x \ (x \text{ free}).
\end{aligned}
$$

The shift is defined when no index crosses its cutoff: there is no index
$i \ge c$ with $i + d < c$, where $c$ is the cutoff at that occurrence. Such
an index would be captured by an enclosing binder, or become negative. A
shift with $d \ge 0$ is always defined.

`shift(t, d, c)` implements it by carrying the binder depth $k$ and testing
$i \ge c + k$, which unfolds the recursion on $c$. A negative $c$ is outside
the domain: it would count indices bound inside $t$ as free, so `shift`
rejects it with `NegativeCutoff` before looking at $t$.

### Substitution of an index

$[j \mapsto s]\,t$ replaces the free index $j$ by $s$:

$$
[j \mapsto s]\,i = \begin{cases} s & i = j \\ i & i \ne j \end{cases}, \qquad
[j \mapsto s]\,(\lambda.\,t) = \lambda.\,[\,j+1 \mapsto \uparrow^{1}_{0} s\,]\,t .
$$

`substitute_bound` unfolds the binder case: under $k$ binders it replaces
index $j + k$ by $\uparrow^{k}_{0} s$. The two agree because shifts with the
same cutoff compose (Lemma 1 below):
$\uparrow^{1}_{0}\cdots\uparrow^{1}_{0} s = \uparrow^{k}_{0} s$.

### Beta reduction

$$
(\lambda.\,t)\;s \;\to_\beta\; \uparrow^{-1}_{0}\big(\,[\,0 \mapsto \uparrow^{1}_{0} s\,]\;t\,\big) .
$$

The argument is shifted up because it moves under the binder of $t$; after
the substitution the binder is removed, so all remaining free indices of the
body are shifted down. This is `instantiate(t, s)`.[^tapl]

[^tapl]: B. C. Pierce, *Types and Programming Languages*, MIT Press 2002, §6.2–6.3.

## Design decisions

### Shifting is checked, not assumed

**Problem.** A downward shift can move a free index below its cutoff. Below
zero the index refers to nothing; between zero and the cutoff it is captured
by an enclosing binder. Either way the result is a silently wrong term.

**Choice.** `shift` returns `Err(NegativeShift)` when a free index would cross
its cutoff and `Err(NegativeCutoff)` for a negative cutoff, and `shift`,
`substitute_bound`, `instantiate`, `validate` and `to_named` report
`NegativeIndex` for any negative index they meet. The lemmas below show that
the error cases are unreachable from well-scoped input, so the `Result` costs
nothing for correct callers and turns a silent corruption into data for
incorrect ones. This follows the library rule that expected failures at
public boundaries are structured values.

The index operations work on open terms, so they cannot tell a dangling
(too large) index from one that points at a binder outside the term:
`instantiate` shifts it like a free index. The reducers work on whole terms
and validate them. `reduce_once` runs `validate` before searching and
returns its error as `ScopeFailure`; `normalize` validates its input once,
and Lemma 2 below shows that the later terms need no check. The search
itself is a private function that is also applied to binder bodies, whose
indices may point at enclosing binders.

### Instantiation never fails on well-scoped input

**Lemma 1 (shift composition).** For $a, b \ge 0$:
$\uparrow^{a}_{c}\uparrow^{b}_{c} t = \uparrow^{a+b}_{c} t$, and
$\uparrow^{0}_{c} t = t$.

On an index $i$ relative to the current cutoff: if $i < c$ both sides leave
it; if $i \ge c$ then $i + b \ge c$, so

$$
\uparrow^{a}_{c}\uparrow^{b}_{c}\, i = (i + b) + a = \uparrow^{a+b}_{c}\, i .
$$

The binder case raises the cutoff on both sides alike. $\square$

**Lemma 2 (safety of the downward shift).** Let $\lambda.\,t$ and $s$ be well
scoped at depth $n$. Then every free index of
$u = [\,0 \mapsto \uparrow^{1}_{0} s\,]\,t$ lies in $\{1, \dots, n\}$, so
$\uparrow^{-1}_{0} u$ succeeds and is well scoped at depth $n$.

The body $t$ is well scoped at depth $n + 1$, so its free indices lie in
$\{0, \dots, n\}$. Follow a free occurrence in $t$ under $k$ inner binders:

$$
\begin{aligned}
i = k + 0 &: \text{replaced by } \uparrow^{k}_{0}\uparrow^{1}_{0} s = \uparrow^{k+1}_{0} s \text{ (Lemma 1)}, \\
&\quad\text{whose free indices relative to the root are } j + 1 \in \{1, \dots, n\} \text{ for } j \in \mathrm{fi}(s) \subseteq \{0, \dots, n-1\}, \\
i = k + m,\ m \ge 1 &: \text{kept, with root-relative index } m \in \{1, \dots, n\}.
\end{aligned}
$$

No free index $0$ remains. Under $k$ binders the shift by $-1$ has cutoff
$k$ and moves the index $k + m$ with $m \ge 1$ to $k + m - 1 \ge k$, so no
index crosses its cutoff, and the root-relative free indices are mapped
$\{1, \dots, n\} \to \{0, \dots, n - 1\}$. $\square$

Hence `instantiate` and `reduce_once` return no `ScopeError` on well-scoped
input, and a reduct of a well-scoped term is well scoped (subject reduction
for scope). Together with the validation of the input, `normalize` returns
`ScopeFailure` exactly when its input is ill scoped, and then with
`steps=0`: `Bind(Bound(-1))` gives `NegativeIndex(index=-1)` and `(λ. 5) 1`
gives `UnboundIndex(index=5, depth=1)`.

The detailed proofs, including the commutation of shifts with different
cutoffs and the De Bruijn substitution lemma, are in the attachment:

[Index lemmas for De Bruijn terms](../../attachments/design_debruijn_index-lemmas.typ)

### Exact translations

`from_named` keeps a stack of binder names and translates an occurrence of
$x$ to the distance to the nearest binder of $x$, or to `Free(x)` if there is
none. `to_named` invents a binder name with `fresh_name("x", U)`, where $U$
contains the free names of the term and the names of the enclosing binders.

**Theorem (round trips).**

1. $\texttt{to\_named}(\texttt{from\_named}(t)) =_\alpha t$ for every named $t$.
2. $\texttt{from\_named}(\texttt{to\_named}(d)) = d$ for every well-scoped $d$.
3. $\texttt{from\_named}(t) = \texttt{from\_named}(u) \iff t =_\alpha u$.

For (2): along any path from the root, the names chosen by `to_named` are
pairwise distinct and distinct from all free names, because each is chosen
fresh for a set that contains the free names and every enclosing binder name.
An occurrence of index $i$ under $n$ binders becomes the name of the binder at
level $n - 1 - i$; translating back, the nearest binder with that name is that
same binder (no other enclosing binder has the name), at distance $i$. A
`Free(x)` becomes $x$, which is not the name of any binder on the path, so it
translates back to `Free(x)`. (3) is de Bruijn's theorem; (1) follows from (2)
and (3), since $\texttt{from\_named}(\texttt{to\_named}(\texttt{from\_named}(t))) = \texttt{from\_named}(t)$.

### Named and nameless beta agree

For named terms, beta is $(\lambda x.\,b)\,a \to b[x := a]$ with the
capture-avoiding substitution of [substitution](substitution.md). Write
$\ulcorner b \urcorner_{x}$ for the translation of $b$ with $x$ as the
innermost binder. Then

$$
\ulcorner b[x := a] \urcorner \;=\; \texttt{instantiate}\big(\ulcorner b \urcorner_{x},\ \ulcorner a \urcorner\big),
$$

by induction on $b$: an occurrence of $x$ under $k$ inner binders has index
$k$ and receives $\uparrow^{k}_{0}\ulcorner a \urcorner$, which is the
translation of $a$ placed under those $k$ binders; at the root $\ulcorner a \urcorner$ has
no free indices, so the shift changes nothing. Renaming of binders by the
named substitution is invisible after translation by (3), and the translation
lemma of the [substitution design](substitution.md) makes this induction
precise. Since the translation also preserves the shape of terms, the
beta-only named reducer (`@eval.evaluate` with `@lambda.beta_rule` and
`NormalOrder`) and `reduce_once` choose the same leftmost-outermost redex, and
one step commutes with translation up to $=_\alpha$. (`@lambda.normalize`
also contracts eta redexes, so its normal forms can be eta-shorter.) The test "named and debruijn beta reduction agree modulo alpha"
checks an instance that needs renaming on the named side.

### Spines and reduction order

`Apply(head, args)` is a curried spine: `Apply(Bind(t), [a, ..rest])` is the
redex $(\lambda.\,t)\,a$ applied to `rest`, and a step contracts only the first
argument. An empty spine `Apply(h, [])` stands for $h$ itself, so empty
applications around the `Bind` are looked through when a redex is matched. `reduce_once` searches root, head, arguments, and enters binders: it
is the normal-order strategy of the [eval design](eval.md) on nameless terms,
so the normalization theorem applies to `normalize`.

### Explicit stacks instead of host recursion

**Problem.** Every operation above is defined by structural recursion on
the term, and a direct implementation keeps one host stack frame per level
of nesting. Terms from users and downstream ASTs can be deep (a long spine
$f\,(f\,(f \cdots))$, a long chain of binders), and the js, wasm and wasm-gc
stacks overflow at a depth of a few thousand, so the same call returned a
result on native and crashed on the other backends.

**Choice.** Each operation runs as a loop over an explicit stack in a heap
array, and visits the subterms in exactly the order of its recursive
definition, so its results, including the error it reports, are unchanged.
The host stack depth is constant; the heap stacks hold at most one entry per
node of the term.

*Checks.* `validate` and `==` keep a stack of the subterms (or pairs of
subterms) still to visit. Write $\mathrm{pre}(t)$ for the nodes of $t$ in
pre-order, head before arguments and arguments from left to right:

$$
\mathrm{pre}(\lambda.\,t) = \lambda \cdot \mathrm{pre}(t), \qquad
\mathrm{pre}(t\,u_1 \cdots u_m) = @ \cdot \mathrm{pre}(t) \cdot \mathrm{pre}(u_1) \cdots \mathrm{pre}(u_m),
$$

and $\mathrm{pre}(a) = a$ for a leaf $a$. The loop pops the top entry, checks
it if it is a leaf, and otherwise pushes its children, $u_m$ first and the
head $t$ last. With the stack $t_1 \cdots t_r$ (top first) it maintains

$$
\mathrm{pre}(t_1) \cdots \mathrm{pre}(t_r) \;=\; \text{the nodes of the input not visited yet, in pre-order},
$$

since popping $t\,u_1 \cdots u_m$ and pushing its children replaces
$\mathrm{pre}(t\,\vec u)$ by its tail. So the leaves are checked in pre-order.
The recursive `validate` returns the first error of its head, else of its
arguments from left to right, which by induction is also the first error in
pre-order. Both return the same error. An index is checked against the
number of binders above it, which the stack stores with each entry.

*Translations.* `shift`, `substitute_bound` (both through one rebuilding
traversal that applies a function to each `Bound(i)` and its binder count),
`from_named` and `to_named` produce a term. They keep a stack of tasks,
$\mathsf{visit}(t, k)$ and $\mathsf{build}_@(m)$ / $\mathsf{build}_\lambda$,
and a stack of results. Visiting a leaf pushes its translation; visiting
$t\,u_1 \cdots u_m$ pushes $\mathsf{build}_@(m)$ and above it the visits of
$u_m, \dots, u_1, t$; $\mathsf{build}_@(m)$ pops the $m + 1$ translations
and pushes the application of the first to the others. By induction on $t$,
running the tasks pushed for $\mathsf{visit}(t, k)$ pushes exactly one
result, the recursive translation of $t$ under $k$ binders, and leaves the
rest of both stacks untouched. Leaves are visited in pre-order as above;
errors arise only at leaves, and both versions stop at the first one, so
they return the same `Err`. In `substitute_bound` the replacement at an
occurrence is shifted by the same loop, run to its end before the
traversal continues.

`from_named` keeps, for each name, the levels of the enclosing binders of
that name, and maps an occurrence under $n$ binders to $n - 1 - \ell$ for
the innermost level $\ell$, the index of the nearest binder of that name.
`to_named` names a binder with the first name of $x, x_1, x_2, \dots$ that
is neither free in the term ($F$) nor the name of an enclosing binder. Let
$c_0, c_1, \dots$ be the names of that sequence not in $F$. By induction on
the level, the enclosing binders of a binder at level $n$ are named
$c_0, \dots, c_{n-1}$, so it gets $c_n$: the name depends only on the level
and is computed once. Both translations are therefore linear in the size of
the term (up to hashing), where a copy of the binder stack at each binder
and a rescan of the candidate names made a chain of $n$ binders cost
$O(n^2)$.

*Reduction.* The recursive search of `reduce_once` tries a node, then its
head, then its arguments from left to right, and enters binder bodies, and
it contracts the first redex it meets: the first redex in pre-order. The
loop walks the term in pre-order and keeps the path from the root, each
ancestor with the child it descended into; when a leaf ends a branch it
returns to the nearest application with an argument left. When it meets a
redex it contracts it, then rebuilds the ancestors from the innermost
outwards and prepends one frame per ancestor to the reduction path, which is
the order in which the recursive calls return. The steps, their paths and
their counts in `normalize` are therefore unchanged.

The tests in `src/debruijn/deep_test.mbt` run every operation on terms
nested to depth 100 000 (application chains in head and in argument
position, binder chains with indices that reach the outermost binder, and
mixtures of these, well scoped and ill scoped) on every backend; before the
change each of them overflowed the stack on js, wasm and wasm-gc.

## Correctness and invariants

- `validate(from_named(t)) == Ok(())` for every named $t$.
- Round trips (1)–(3) above; `==` on well-scoped `DbTerm` is alpha-equivalence.
- Lemma 2: on well-scoped input `instantiate` succeeds and preserves scope;
  `reduce_once` never returns `ScopeFailure`, and every reduct is well scoped.
  On ill-scoped input `reduce_once` and `normalize` return `ScopeFailure`
  with the error `validate` reports.
- `reduce_once` satisfies the one-redex contract of
  [rewrite](rewrite.md), with rule name `"beta"`.
- `shift(t, 0, c) == Ok(t)` for every `t` without negative indices, and
  shifts with one cutoff compose (Lemma 1).
- `shift` never turns a free index into a bound one: if a free index would
  fall below its cutoff, it returns `Err(NegativeShift)`, and it rejects a
  negative cutoff, which would free bound indices, with `Err(NegativeCutoff)`.

Cost: `shift`, `validate`, `from_named` and `to_named` are linear in the term
size (the translations up to hashing of names). `substitute_bound`
costs $O(|t| + m \cdot |s|)$ for $m$ occurrences of the index, because each
inserted copy is shifted. A `reduce_once` step costs one search plus one
`instantiate`, plus building the reduction path, which has one frame per
ancestor of the redex and is built with `@rewrite.ReductionPath::prepend`.

Stack: every operation uses a constant depth of host stack, whatever the
nesting depth of the term; its pending work is kept in heap arrays with at
most one entry per node.

## Alternatives rejected

- **Levels instead of indices in syntax.** Levels make weakening free but
  substitution under binders more complex; indices are the standard for
  syntax, and levels are used where they help (NbE).
- **Fully nameless free variables.** Free variables are kept as names so that
  open terms from users and downstream ASTs need no global variable
  numbering, and so that `to_named` can restore them exactly.
- **Explicit substitutions.** A calculus with suspended substitutions avoids
  repeated shifting but complicates every consumer; the NbE package provides
  the efficient path instead.

## Boundaries

- Binder names are not preserved: `to_named` chooses `x`, `x_1`, ….
- `shift`, `substitute_bound` and `instantiate` operate on open terms and do
  not detect dangling indices; the reducers and `validate` do.
- An empty application `Apply(h, [])` is read as `h` when a redex is matched,
  so it never hides a redex, but `reduce_once` leaves the node in place,
  whereas [utlc/nbe](utlc/nbe.md) drops it from its normal forms.
- Only beta is implemented; there is no eta rule for De Bruijn terms.
- Values are opaque; their contents are never shifted.
- The derived `Debug` of `DbTerm` (and of the result types that contain one)
  recurses over the term, so printing a deeply nested term can overflow the
  host stack on js, wasm and wasm-gc. Every other operation, `==` included,
  handles any nesting depth.
