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

## Constraints

- **Divergence.** Untyped terms need not normalize, so every phase must be
  bounded, and only by the budget: a divergent run must end with
  `FuelExhausted` on every backend, whatever the size of the host stack.
- **Reproducibility.** The outcome must not depend on anything but the input
  and the budget, and the reported cost must be exact.
- **Encapsulation.** Callers must not be able to build semantic values that
  break the evaluator's scope invariant.

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
$f' \ge c$. The fuel is only tested by `fuel <= 0`, and every test that
passes is followed by spending one unit. If $s$ units have been spent before
some test of the original run, that test is followed by at least one more
unit, so $s + 1 \le c$; with fuel $f'$ the test sees
$f' - s \ge c - s \ge 1$ and passes as well. Every test of the original run
therefore passes again, the run takes the same path, and it stops with the
same result. With $f' = c - 1$ the last test sees $0$ and fails. Results are
therefore reproducible, and `consumed` is the exact minimum budget for that
result.

### A bounded host stack

**Problem.** Written as host functions, the equations of evaluation and
readback are mutually recursive, and every call whose result is still
needed keeps a host stack frame. On $\Omega$, applying
$\mathsf{clo}(0\,0, [\,])$ evaluates $0\,0$, which applies the closure
again, and none of these calls returns before the fuel runs out: the host
stack grows with the fuel spent. The js, wasm and wasm-gc stacks are much
smaller than a budget of a few million units needs, so such a run overflowed
the stack instead of ending with `FuelExhausted`, against the constraint
that every phase is bounded. Readback has the same problem on a term with an
infinite normal form, such as $(\lambda.\,f\,(0\,0))\,(\lambda.\,f\,(0\,0))$,
whose readback $f\,(f\,(f \cdots))$ nests one call of $R_n$ per argument.

**Choice.** Evaluation runs as an abstract machine whose continuation is an
explicit stack of frames in the heap: the recursive evaluator in
continuation-passing style with the continuations defunctionalized, in the
manner of the CEK machine.[^machines] A state
$\langle c \mid K \mid f \rangle$ consists of a control $c$, a continuation
$K$ (a list of frames, top first) and the remaining fuel $f$:

$$
c \;::=\; \mathsf{ev}(t, \rho) \;\mid\; \mathsf{fo}(d) \;\mid\; \mathsf{ret}(d), \qquad
k \;::=\; \mathsf{spine}(\vec u, j, \rho) \;\mid\; \mathsf{to}(e), \qquad
K \;::=\; \varepsilon \;\mid\; k \cdot K .
$$

$\mathsf{ev}$ and $\mathsf{fo}$ are calls of $\llbracket - \rrbracket$ and
$\mathrm{force}$; $\mathsf{ret}(d)$ passes a value to the top frame.
$\mathsf{spine}(\vec u, j, \rho)$, for the arguments
$\vec u = u_0 \cdots u_{m-1}$ of an application node, waits for the value to
apply to $\mathsf{delay}(u_j, \rho), \ldots, \mathsf{delay}(u_{m-1}, \rho)$;
$\mathsf{to}(e)$ waits for a forced function to apply to $e$. In the code
these are `EvalControl` (`Evaluate`, `Force`, `Return`) and `EvalFrame`
(`ApplyArguments`, `ApplyTo`). The rules for $\mathsf{ev}$ and
$\mathsf{fo}$ apply when $f \ge 1$; with $f \le 0$ the machine stops with
`FuelExhausted`, and an index outside $\rho$ stops it with `ScopeFailure`:

$$
\begin{aligned}
\langle \mathsf{ev}(v, \rho) \mid K \mid f \rangle &\to \langle \mathsf{ret}(\mathsf{atom}(v)) \mid K \mid f - 1 \rangle \\
\langle \mathsf{ev}(x, \rho) \mid K \mid f \rangle &\to \langle \mathsf{ret}(\mathsf{free}(x)) \mid K \mid f - 1 \rangle \\
\langle \mathsf{ev}(i, \rho) \mid K \mid f \rangle &\to \langle \mathsf{fo}(\rho_i) \mid K \mid f - 1 \rangle \\
\langle \mathsf{ev}(\lambda.\,t, \rho) \mid K \mid f \rangle &\to \langle \mathsf{ret}(\mathsf{clo}(t, \rho)) \mid K \mid f - 1 \rangle \\
\langle \mathsf{ev}(t\,\vec u, \rho) \mid K \mid f \rangle &\to \langle \mathsf{ev}(t, \rho) \mid \mathsf{spine}(\vec u, 0, \rho) \cdot K \mid f - 1 \rangle \quad (m \ge 1) \\
\langle \mathsf{fo}(\mathsf{delay}(t, \rho)) \mid K \mid f \rangle &\to \langle \mathsf{ev}(t, \rho) \mid K \mid f - 1 \rangle \\
\langle \mathsf{fo}(d) \mid K \mid f \rangle &\to \langle \mathsf{ret}(d) \mid K \mid f - 1 \rangle \quad (d \text{ not delayed}) \\
\langle \mathsf{ret}(d) \mid \mathsf{spine}(\vec u, j, \rho) \cdot K \mid f \rangle &\to \langle \mathsf{fo}(d) \mid \mathsf{to}(\mathsf{delay}(u_j, \rho)) \cdot K' \mid f \rangle \\
\langle \mathsf{ret}(\mathsf{clo}(t, \rho)) \mid \mathsf{to}(e) \cdot K \mid f \rangle &\to \langle \mathsf{ev}(t, e \cdot \rho) \mid K \mid f \rangle \\
\langle \mathsf{ret}(d) \mid \mathsf{to}(e) \cdot K \mid f \rangle &\to \langle \mathsf{ret}(\mathsf{app}(d, e)) \mid K \mid f \rangle \quad (d \text{ not a closure})
\end{aligned}
$$

where $K' = \mathsf{spine}(\vec u, j + 1, \rho) \cdot K$ if $j + 1 < m$ and
$K' = K$ otherwise. An empty application $t\,()$ steps to
$\langle \mathsf{ev}(t, \rho) \mid K \mid f - 1 \rangle$. The machine starts
in $\langle \mathsf{ev}(t, \rho) \mid \varepsilon \mid f \rangle$ (or
$\mathsf{fo}(d)$) and returns $d$ with $f$ units left when it reaches
$\langle \mathsf{ret}(d) \mid \varepsilon \mid f \rangle$.

*Same values.* Read a continuation as the function it still has to apply,

$$
\begin{aligned}
\varepsilon(d) &= d, \qquad
(\mathsf{to}(e) \cdot K)(d) = K\big(\mathrm{app}(d, e)\big), \\
(\mathsf{spine}(\vec u, j, \rho) \cdot K)(d) &= K\big(\mathrm{app}(\cdots\mathrm{app}(d, \mathsf{delay}(u_j, \rho))\cdots, \mathsf{delay}(u_{m-1}, \rho))\big),
\end{aligned}
$$

and a state $\langle c \mid K \mid f \rangle$ as $K(\overline{c})$ with
$\overline{\mathsf{ev}(t, \rho)} = \llbracket t \rrbracket\rho$,
$\overline{\mathsf{fo}(d)} = \mathrm{force}(d)$ and
$\overline{\mathsf{ret}(d)} = d$. Every rule turns a state into one with the
same reading, by one of the evaluation equations above: the first seven
rules are the equations of $\llbracket - \rrbracket$ and $\mathrm{force}$,
the $\mathsf{spine}$ rule unfolds the leftmost application of the spine,
starting it as the implementation does by forcing the function, and the two
$\mathsf{to}$ rules are the two equations of $\mathrm{app}$. When
$j + 1 = m$ no frame for the remaining arguments is needed, since
$\mathsf{spine}(\vec u, m, \rho) \cdot K$ reads as $K$. By induction on the
number of steps, a run that stops at $\langle \mathsf{ret}(d) \mid
\varepsilon \mid f' \rangle$ computes $d = \llbracket t \rrbracket\rho$.

*Same fuel.* Units are tested and spent exactly in the
$\mathsf{ev}$ and $\mathsf{fo}$ rules, that is on entry to
$\llbracket - \rrbracket$ and $\mathrm{force}$, where the recursive
functions test and spend them; the $\mathsf{ret}$ rules spend nothing, like
returning from a host call and dispatching on its result. The machine makes
the calls in the order of the recursive definition (it is that definition
with its host stack made explicit), so every test sees the same remaining
fuel. Results, `consumed`, and the determinism argument above are therefore
unchanged; the tests pin exact costs from before the change.

*Bounded stacks.* The machine is a single loop, so its host stack depth is
constant. The frame stack $K$ grows only in the
$\mathsf{ev}(t\,\vec u, \rho)$ rule, which spends a unit, and in the
$\mathsf{spine}$ rule, which replaces one frame by at most two and is
followed by a $\mathsf{fo}$ step that spends a unit or stops. Hence, at
every step,

$$
|K| \;\le\; \text{units spent so far} + 1 \;\le\; f_0 + 1 ,
$$

and the pending work lives in the heap, bounded by the initial budget $f_0$.
On $\Omega$ the stack never holds more than one frame: applying the closure
to the last argument of the spine leaves nothing below the
$\mathsf{to}$ frame, and the $\mathsf{to}$ rule pops it before the body is
evaluated, so this tail call runs in constant space. A term that grows, such
as $(\lambda.\,0\,0\,0)\,(\lambda.\,0\,0\,0)$, keeps one
$\mathsf{spine}$ frame per unfolding for its last argument; its stack grows
in the heap, within the bound.

Readback is transformed in the same way, with controls
$\mathsf{rb}(d, n)$ (read $d$ back under $n$ binders) and
$\mathsf{emit}(u)$ (pass a term to the top frame) and frames

$$
q \;::=\; \mathsf{bind} \;\mid\; \mathsf{arg}(e, n) \;\mid\; \mathsf{head}(s)
$$

(`QuoteControl` and `QuoteFrame` in the code). A step
$\mathsf{rb}(d, n)$ spends one unit and forces $d$ to $d'$; a constant, a
free name or a level emits the corresponding term, an application
$\mathsf{app}(d_1, e)$ continues with $\mathsf{rb}(d_1, n)$ under the frame
$\mathsf{arg}(e, n)$, and a closure $\mathsf{clo}(t, \rho)$ evaluates $t$ in
$\mathsf{lvl}(n) \cdot \rho$ to $d''$ and continues with
$\mathsf{rb}(d'', n + 1)$ under $\mathsf{bind}$. An emitted $u$ meets its
frame:

$$
\langle \mathsf{emit}(u) \mid \mathsf{bind} \cdot Q \rangle \to \langle \mathsf{emit}(\lambda.\,u) \mid Q \rangle, \quad
\langle \mathsf{emit}(u) \mid \mathsf{arg}(e, n) \cdot Q \rangle \to \langle \mathsf{rb}(e, n) \mid \mathsf{head}(u) \cdot Q \rangle, \quad
\langle \mathsf{emit}(u) \mid \mathsf{head}(s) \cdot Q \rangle \to \langle \mathsf{emit}(s\,u) \mid Q \rangle .
$$

These are the readback equations above, with the head of a neutral
read before its argument as before. The forcing and the evaluation inside an
$\mathsf{rb}$ step run the evaluation machine to its end and return to the
readback loop, so the host stack holds at most the two loops, and $Q$, like
$K$, is bounded by the units spent.

[^machines]: M. Felleisen and D. P. Friedman, "Control operators, the SECD-machine, and the λ-calculus", 1986, for the CEK machine; M. S. Ager, D. Biernacki, O. Danvy and J. Midtgaard, "A functional correspondence between evaluators and abstract machines", PPDP 2003, for deriving it from an evaluator by CPS transformation and defunctionalization.

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

## Correctness and invariants

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
for the same well-scoped term, the two normal forms are equal after spine
flattening, which merges nested applications and drops empty ones. Both read
`Apply(h, [])` as $h$: evaluation erases the node, and the small-step reducer
looks through it when it matches a redex (see the
[eval design](../eval.md)). The
tests in `src/utlc/nbe/nbe_test.mbt` check this, laziness on
$(\lambda.\,7)\,\Omega$, fuel exhaustion on $\Omega$, and that quote turns
levels back into indices. Further tests run $\Omega$, a divergent term whose
head grows, and two terms with infinite normal forms with budgets of thirty
million units on every backend, and pin the exact cost of Church numeral
arithmetic together with its reproducibility at `consumed` and
`consumed - 1`.

Other invariants:

- With positive fuel, `eval` and `normalize` reject ill-scoped input with
  `ScopeFailure` and `consumed=0` before doing any work; with fuel `<= 0`
  they return `FuelExhausted(consumed=0)` without looking at the term.
- `quote(value, n, _)` returns `ScopeFailure` only when $n < 0$ or a level
  variable is not below $n$. Values produced by `eval` contain no level
  variables, so quoting them at any level $n \ge 0$ never fails this way.
- Fuel: `consumed` never exceeds the fuel given; the determinism property
  above holds.
- Stack: evaluation and readback use a constant depth of host stack; their
  frame stacks live in the heap and are bounded by the budget.

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
- **Direct recursion with a larger stack.** The js and wasm hosts fix the
  stack size, and any fixed stack is exhausted by some budget, so the outcome
  would depend on the backend.
- **Trampolining through host closures.** Returning a closure for the rest of
  the computation also bounds the stack, but allocates a host function per
  step and hides the pending work. First-order frames keep the machine
  observable, for the same reason as first-order semantic closures.

## Boundaries

- Beta only: no eta, no reduction of constants.
- Not total: `FuelExhausted` is the expected outcome for divergent terms and
  does not prove divergence.
- No sharing of delayed arguments.
- Only evaluation and readback have a bounded host stack. `eval` and
  `normalize` first validate their input with `@debruijn.validate`, which
  recurses over the term, so the stack depth they need still grows with the
  nesting depth of the input term.
- Normal forms use unary applications.
- Input must be De Bruijn syntax; convert named terms with
  `@debruijn.from_named` and results back with `@debruijn.to_named`.
