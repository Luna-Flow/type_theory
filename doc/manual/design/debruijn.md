# debruijn design

## Design goal

Named syntax needs fresh names and renaming in every binder-crossing
operation. `debruijn` provides a representation in which alpha-equivalence is
syntactic equality and beta reduction needs no renaming at all, together with
exact translations to and from named syntax. It is the kernel representation
of the untyped NbE in [utlc/nbe](utlc/nbe.md) and a reference reducer against
which the named calculus in [utlc/lambda](utlc/lambda.md) is tested.

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
cutoff $c$:

$$
\begin{aligned}
\uparrow^{d}_{c}\,i &= \begin{cases} i & i < c \\ i + d & i \ge c \end{cases}, &
\uparrow^{d}_{c}\,(\lambda.\,t) &= \lambda.\,\uparrow^{d}_{c+1} t, \\
\uparrow^{d}_{c}\,(t\,\bar u) &= (\uparrow^{d}_{c} t)\,(\overline{\uparrow^{d}_{c} u}), &
\uparrow^{d}_{c}\,v &= v, \quad \uparrow^{d}_{c}\,x = x \ (x \text{ free}).
\end{aligned}
$$

`shift(t, d, c)` implements it by carrying the binder depth $k$ and testing
$i \ge c + k$, which unfolds the recursion on $c$.

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

**Problem.** A negative shift on an ill-formed term yields a negative index,
which silently refers to nothing.

**Choice.** `shift` returns `Err(NegativeShift)` instead, and every operation
reports `NegativeIndex` on negative input. The lemmas below show that the
error cases are unreachable from well-scoped input, so the `Result` costs
nothing for correct callers and turns a silent corruption into data for
incorrect ones. This follows the library rule that expected failures at
public boundaries are structured values.

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

No free index $0$ remains, so the shift by $-1$ maps
$\{1, \dots, n\} \to \{0, \dots, n - 1\}$ without a negative result. $\square$

Hence `instantiate` and `reduce_once` return no `ScopeError` on well-scoped
input, and a reduct of a well-scoped term is well scoped (subject reduction
for scope). A `ScopeFailure` from `normalize` therefore always means that the
input was ill scoped.

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
translation of $a$ placed under those $k$ binders; renaming of binders by the
named substitution is invisible after translation by (3). Since the
translation also preserves the shape of terms, the two reducers choose the
same leftmost-outermost redex, and one step commutes with translation up to
$=_\alpha$. The test "named and debruijn beta reduction agree modulo alpha"
checks an instance that needs renaming on the named side.

### Spines and reduction order

`Apply(head, args)` is a curried spine: `Apply(Bind(t), [a, ..rest])` is the
redex $(\lambda.\,t)\,a$ applied to `rest`, and a step contracts only the first
argument. `reduce_once` searches root, head, arguments, and enters binders: it
is the normal-order strategy of the [eval design](eval.md) on nameless terms,
so the normalization theorem applies to `normalize`.

## Correctness / invariants

- `validate(from_named(t)) == Ok(())` for every named $t$.
- Round trips (1)–(3) above; `==` on well-scoped `DbTerm` is alpha-equivalence.
- Lemma 2: on well-scoped input `instantiate` succeeds and preserves scope;
  `reduce_once` never returns `ScopeFailure`, and every reduct is well scoped.
- `reduce_once` satisfies the one-redex contract of
  [rewrite](rewrite.md), with rule name `"beta"`.
- `shift(t, 0, c) == Ok(t)` and shifts with one cutoff compose (Lemma 1).

Cost: `shift` and `validate` are linear in the term size. `substitute_bound`
costs $O(|t| + m \cdot |s|)$ for $m$ occurrences of the index, because each
inserted copy is shifted. A `reduce_once` step costs one search plus one
`instantiate`.

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
- `substitute_bound` and `reduce_once` do not detect unbound indices; call
  `validate` on untrusted input.
- Only beta is implemented; there is no eta rule for De Bruijn terms.
- Values are opaque; their contents are never shifted.
