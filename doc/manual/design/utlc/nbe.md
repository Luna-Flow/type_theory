# utlc/nbe design

## Design goal

Small-step normalization repeats a search from the root for every beta step
and copies the term each time. *Normalization by evaluation* (NbE) instead
interprets a term as a value of the host language, where beta reduction is
just function application, and reads the value back as a normal form. This
package provides NbE for the untyped calculus on [De Bruijn terms](../debruijn.md):
fast, but bounded by fuel, because untyped terms need not normalize. The
operational reducers remain the reference semantics; NbE is checked against
them.

## Mathematical background

### The semantic domain

Values are given by the following grammar, where $\rho$ is an environment (a
list of values, index $0$ first), $t$ a De Bruijn term, $x$ a free name and
$\ell$ a level:

$$
\begin{aligned}
d \in D \;&::=\; \mathsf{atom}(v) \;\mid\; \mathsf{clo}(t, \rho) \;\mid\; \mathsf{delay}(t, \rho) \;\mid\; n, \\
n \in \mathrm{Ne} \;&::=\; \mathsf{free}(x) \;\mid\; \mathsf{lvl}(\ell) \;\mid\; \mathsf{app}(d, d).
\end{aligned}
$$

$\mathsf{clo}(t, \rho)$ is the value of $\lambda.\,t$ in $\rho$;
$\mathsf{delay}(t, \rho)$ is an argument not yet evaluated; neutral values
$n$ are computations stuck on a variable. In the implementation,
$\mathsf{app}(d, e)$ also arises when $d$ is a constant, since a constant
applied to an argument is stuck as well.

### Evaluation

$\llbracket t \rrbracket\rho$ evaluates to weak head form:

$$
\begin{aligned}
\llbracket v \rrbracket\rho &= \mathsf{atom}(v), &
\llbracket x \rrbracket\rho &= \mathsf{free}(x), &
\llbracket i \rrbracket\rho &= \mathrm{force}(\rho_i), \\
\llbracket \lambda.\,t \rrbracket\rho &= \mathsf{clo}(t, \rho), &
\llbracket t\,u_1 \cdots u_n \rrbracket\rho &= \mathrm{app}(\cdots\mathrm{app}(\llbracket t \rrbracket\rho, \mathsf{delay}(u_1, \rho))\cdots, \mathsf{delay}(u_n, \rho)),
\end{aligned}
$$

$$
\mathrm{app}(\mathsf{clo}(t, \rho), e) = \llbracket t \rrbracket(e \cdot \rho), \qquad
\mathrm{app}(d, e) = \mathsf{app}(d, e) \ \text{otherwise}, \qquad
\mathrm{force}(\mathsf{delay}(t, \rho)) = \llbracket t \rrbracket\rho .
$$

Arguments are delayed, so evaluation is *call by name*: an argument that is
never used is never evaluated. There is no memoization; a delayed argument
used twice is evaluated twice.

### Readback

$R_n(d)$ reads $d$ back under $n$ binders:

$$
\begin{aligned}
R_n(\mathsf{atom}(v)) &= v, &
R_n(\mathsf{free}(x)) &= x, &
R_n(\mathsf{lvl}(\ell)) &= n - 1 - \ell, \\
R_n(\mathsf{clo}(t, \rho)) &= \lambda.\, R_{n+1}\big(\llbracket t \rrbracket(\mathsf{lvl}(n) \cdot \rho)\big), &
R_n(\mathsf{app}(d, e)) &= R_n(d)\; R_n(e), &
R_n(\mathsf{delay}(t,\rho)) &= R_n(\llbracket t \rrbracket\rho).
\end{aligned}
$$

A closure is read back by applying it to a fresh variable. That variable is
represented by its *level* $n$, which does not change while the value is
carried under further binders, and converted to the index $n - 1 - \ell$ at
the occurrence (see levels in the [debruijn design](../debruijn.md)).
`normalize(t)` is $R_0(\llbracket t \rrbracket[\,])$ for closed $t$.

## Design decisions

### Untyped NbE needs a budget

**Problem.** For $\Omega = (\lambda.\,0\,0)(\lambda.\,0\,0)$, evaluation
unfolds $\mathrm{app}(\mathsf{clo}(0\,0, [\,]), \cdot)$ forever. In the typed
setting termination is a theorem ([stlc design](../stlc.md)); here it is
false.

**Choice.** Every evaluation of a node, every `force` and every readback
step costs one unit of fuel, and running out yields `FuelExhausted` with the
amount consumed. The budget is threaded through all phases, so the cost of
reading back under binders, which may evaluate closure bodies, is included.

**Determinism in the budget.** The computation does not inspect the fuel
except to stop, so a run with fuel $f$ that ends with a normal form after
consuming $c \le f$ units performs exactly the same computation with any fuel
$f' \ge c$. Results are therefore reproducible, and `consumed` is the exact
minimum budget for that result.

### Laziness without sharing

**Problem.** Strict evaluation (call by value) diverges on
$(\lambda.\,7)\,\Omega$, although the term has the normal form $7$.

**Choice.** Arguments are delayed. Together with readback, which evaluates
the head of every neutral first and its arguments afterwards, and enters
closures only after their head is known, this realizes normal-order
(leftmost-outermost) reduction, the normalizing strategy of the
[eval design](../eval.md). Call by need would share delayed results; it is not
used because it needs mutable thunks, and the budget keeps the cost of
recomputation bounded and visible.

### Opaque semantic values

`Semantic[T]` is a struct around a private enum. Callers can create neutral
values (`reflect_free`, `reflect_level`), evaluate, and quote, but cannot
build closures with ill-scoped environments. This keeps the invariant that
every closure environment matches the scope of its body, which is why `eval`
validates its input once and can then trust every index lookup.

### Unary applications in normal forms

Readback produces $R_n(\mathsf{app}(d, e)) = R_n(d)\,R_n(e)$ as a unary
`Apply`, so the spine $f\,a\,b$ is returned as `Apply(Apply(f, [a]), [b])`.
The small-step reducer keeps the n-ary `Apply(f, [a, b])` of its input. Both
denote the same curried application; comparisons between the two normalizers
must flatten spines first.

## Correctness / invariants

**Theorem (soundness).** If `normalize(t, fuel)` returns `NormalForm(u, _)`,
then $u$ is beta-normal and $t =_\beta u$ (up to spine flattening).

*Sketch.* Define the *denotation* $\lfloor d \rfloor_n$ of a value under $n$
binders as the term it stands for: $\lfloor \mathsf{clo}(t, \rho) \rfloor_n = \lambda.\,t[\rho]$,
$\lfloor \mathsf{delay}(t, \rho) \rfloor_n = t[\rho]$, $\lfloor \mathsf{lvl}(\ell) \rfloor_n = n - 1 - \ell$,
and so on, where $t[\rho]$ substitutes the denotations of $\rho$ for the free
indices of $t$. By induction on evaluation, $t[\rho] \to_\beta^{*} \lfloor \llbracket t \rrbracket\rho \rfloor_n$:
the only non-trivial case is $\mathrm{app}(\mathsf{clo}(t, \rho), e)$, which is
the beta step $(\lambda.\,t[\rho])\,\lfloor e \rfloor \to_\beta t[\lfloor e \rfloor \cdot \rho]$
(substitution lemma of the [debruijn attachment](../../../attachments/design_debruijn_index-lemmas.typ)).
Readback inserts only beta steps under binders, so $t \to_\beta^{*} u$. For
normality: $R$ produces $\lambda$ only from closures, and applications only
from $\mathsf{app}(d, e)$, whose head $d$ is a neutral or a constant, never a
closure (application of a closure is evaluated, not stored). Hence the output
follows the grammar

$$
\mathit{nf} \;::=\; \lambda.\,\mathit{nf} \;\mid\; \mathit{ne}, \qquad
\mathit{ne} \;::=\; x \;\mid\; i \;\mid\; v \;\mid\; \mathit{ne}\;\mathit{nf},
$$

which contains no redex $(\lambda.\,t)\,u$. $\square$

**Completeness (sketch).** If $t$ has a beta normal form, `normalize`
returns it for sufficient fuel. Evaluation computes the weak head normal form
by call by name, and readback recursively normalizes the body of a closure
and the arguments of a neutral after its head: this is the leftmost-outermost
strategy decomposed into head and arguments. By the normalization theorem
(Barendregt 13.2.2) this strategy terminates on every term with a normal
form, and by confluence the normal form is unique.[^nbe]

[^nbe]: For untyped NbE see K. Aehlig and F. Joachimski, "Operational aspects of untyped normalisation by evaluation", Mathematical Structures in Computer Science 14, 2004; for strong reduction by evaluation, B. Grégoire and X. Leroy, "A compiled implementation of strong reduction", ICFP 2002.

**Agreement with small-step reduction.** By soundness and confluence,
whenever both `@nbe.normalize` and `@debruijn.normalize` return a normal form
for the same term, the two normal forms are equal after spine flattening. The
tests in `src/utlc/nbe/nbe_test.mbt` check this, laziness on
$(\lambda.\,7)\,\Omega$, fuel exhaustion on $\Omega$, and that quote turns
levels back into indices.

Other invariants:

- `eval` and `normalize` reject ill-scoped input with `ScopeFailure` and
  `consumed=0` before doing any work.
- `quote(value, n, _)` returns `ScopeFailure` only when a level variable is not
  below $n$, which cannot happen for values produced by `eval` and quoted at
  level 0.
- Fuel: `consumed` never exceeds the fuel given; the determinism property
  above holds.

## Alternatives rejected

- **Typed or eta-long readback.** Untyped readback cannot know where to
  eta-expand; eta-long normal forms are provided for typed terms by
  [stlc](../stlc.md).
- **Host-language closures (HOAS).** Representing $\mathsf{clo}$ as a MoonBit
  function would be faster but makes fuel accounting and inspection of values
  impossible, and the values could not be quoted without a fresh-variable
  trick on the host side. A first-order closure keeps everything observable.
- **Named environments.** Indexing the environment by De Bruijn index makes
  lookup positional and needs no fresh names during evaluation.

## Boundaries

- Beta only: no eta, no reduction of constants.
- Not total: `FuelExhausted` is the expected outcome for divergent terms and
  does not prove divergence.
- No sharing of delayed arguments.
- Normal forms use unary applications.
- Input must be De Bruijn syntax; convert named terms with
  `@debruijn.from_named` and results back with `@debruijn.to_named`.
