# stlc design

## Design goal

`stlc` is a small, complete instance of a typed calculus on the shared
substrate: it reuses the named syntax, substitution, rewriting and the
untyped reducer, and adds what types make possible: a decidable type checker
and a normalizer that needs no step limit and returns canonical
(beta-normal, eta-long) forms. It is the model for richer typed cores built on
`type_theory`.

## Constraints

- **Shared syntax.** Terms are the unannotated `Term[Atom]`, so the shared
  analyses, substitution and rewriting apply unchanged.
- **Decidability.** Type checking must terminate on every input, and
  normalization of well-typed terms must need no step limit.
- **Errors are values.** Every rejection is a `TypeError`.

## Mathematical background

### Types and terms

$$
\tau, \sigma \;::=\; b \;\mid\; \mathsf{Unit} \;\mid\; \sigma \to \tau,
\qquad
t \;::=\; () \;\mid\; c \;\mid\; x \;\mid\; \lambda x.\,t \;\mid\; t\,u_1 \cdots u_n .
$$

Base types $b$ are uninterpreted names. Lambdas carry no type annotation
(Curry style). A *signature* $\Sigma$ gives the types of constants $c$, a
*context* $\Gamma$ the types of free variables; in both, a later entry for a
name shadows an earlier one, written $\Gamma, x{:}\sigma$.

### Declarative typing

The judgement $\Sigma; \Gamma \vdash t : \tau$ is given by the standard
rules ($\Sigma$ is left implicit):

$$
\frac{}{\Gamma \vdash () : \mathsf{Unit}}
\qquad
\frac{\Sigma(c) = \tau}{\Gamma \vdash c : \tau}
\qquad
\frac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau}
\qquad
\frac{\Gamma, x{:}\sigma \vdash t : \tau}{\Gamma \vdash \lambda x.\,t : \sigma \to \tau}
\qquad
\frac{\Gamma \vdash f : \sigma \to \tau \qquad \Gamma \vdash a : \sigma}{\Gamma \vdash f\,a : \tau}
$$

Equality of terms is $\beta\eta$-conversion, with
$(\lambda x.\,b)\,a =_\beta b[x := a]$ and $\lambda x.\,f\,x =_\eta f$ for
$x \notin \mathrm{FV}(f)$, both at well-typed instances.

### Classical results

- **Subject reduction.** If $\Gamma \vdash t : \tau$ and $t \to_{\beta\eta} u$
  then $\Gamma \vdash u : \tau$.
- **Strong normalization.** Every reduction sequence of a well-typed term is
  finite (Tait's method of computability predicates).[^tait]
- **Canonical forms.** Every well-typed term is $\beta\eta$-equal to a unique
  term in *beta-normal, eta-long* form, defined below.

[^tait]: W. W. Tait, "Intensional interpretations of functionals of finite type I", Journal of Symbolic Logic 32, 1967.

## Design decisions

### Bidirectional type checking

**Problem.** Without annotations on lambdas, the type of $\lambda x.\,x$ is
not determined, and full type inference (unification) is more than the
calculus needs.

**Choice.** Two mutually recursive judgements: inference
$\Gamma \vdash t \Rightarrow \tau$ (`infer`) and checking
$\Gamma \vdash t \Leftarrow \tau$ (`check`). Information flows from the
expected type into lambdas, and from variables and constants out of
applications.[^bidir] The implemented rules are

$$
\frac{}{\Gamma \vdash () \Rightarrow \mathsf{Unit}}
\qquad
\frac{\Sigma(c) = \tau}{\Gamma \vdash c \Rightarrow \tau}
\qquad
\frac{\Gamma(x) = \tau}{\Gamma \vdash x \Rightarrow \tau}
$$

$$
\textsc{App}\;
\frac{\Gamma \vdash h \Rightarrow \tau_1 \to \cdots \to \tau_n \to \tau \qquad \Gamma \vdash a_i \Leftarrow \tau_i \ \ (1 \le i \le n)}
     {\Gamma \vdash h\,a_1 \cdots a_n \Rightarrow \tau}
\quad (h \text{ not a } \lambda,\ n \ge 1)
$$

$$
\textsc{Redex}\;
\frac{\Gamma \vdash a_1 \Rightarrow \sigma \qquad \Gamma, x'{:}\sigma \vdash b\{x \mapsto x'\}\,a_2 \cdots a_n \Rightarrow \tau}
     {\Gamma \vdash (\lambda x.\,b)\,a_1\,a_2 \cdots a_n \Rightarrow \tau}
\qquad
\textsc{Redex}^{\Leftarrow}\;
\frac{\Gamma \vdash a_1 \Rightarrow \sigma \qquad \Gamma, x'{:}\sigma \vdash b\{x \mapsto x'\}\,a_2 \cdots a_n \Leftarrow \tau}
     {\Gamma \vdash (\lambda x.\,b)\,a_1\,a_2 \cdots a_n \Leftarrow \tau}
\quad (n \ge 1)
$$

$$
\textsc{Lam}\;
\frac{\Gamma, x{:}\sigma \vdash b \Leftarrow \tau}{\Gamma \vdash \lambda x.\,b \Leftarrow \sigma \to \tau}
\qquad
\textsc{Sub}\;
\frac{\Gamma \vdash t \Rightarrow \tau' \qquad \tau' = \tau}{\Gamma \vdash t \Leftarrow \tau}
$$

In $\textsc{App}$ the spine is flattened first, so nested `Apply` nodes are one
application $h\,a_1 \cdots a_n$; if $h$ has fewer arrows than arguments the
result is `ExpectedFunction`, and an `Apply` node of the spine without
arguments gives `EmptyApplication`. $\textsc{Redex}$ and
$\textsc{Redex}^{\Leftarrow}$ differ only in the mode of the second premise;
in both the spine is flattened in the same way and the parameter is renamed
apart from the trailing arguments:

$$
x' =
\begin{cases}
x & \text{if } x \notin \mathrm{FV}(a_2, \dots, a_n),\\
\operatorname{fresh}\big(x,\ \mathrm{names}(b) \cup \mathrm{names}(a_2, \dots, a_n) \cup \operatorname{dom}\Gamma \cup \{x\}\big) & \text{otherwise,}
\end{cases}
$$

with $b\{x \mapsto x'\}$ the checked bound renaming of the
[syntax design](syntax.md); in both cases
$\lambda x.\,b =_\alpha \lambda x'.\,b\{x \mapsto x'\}$ and
$x' \notin \mathrm{FV}(a_2, \dots, a_n)$. With $n = 1$ there is nothing to
rename and the second premise is $\Gamma, x{:}\sigma \vdash b \Rightarrow \tau$,
or $\Gamma, x{:}\sigma \vdash b \Leftarrow \tau$ for $\textsc{Redex}^{\Leftarrow}$. `check` uses
$\textsc{Redex}^{\Leftarrow}$ for every application whose flattened head is a
lambda, and $\textsc{Sub}$ for every other term except a lambda checked
against an arrow; a lambda in inference position fails with
`CannotInferLambda`. Type equality in $\textsc{Sub}$ is syntactic, which is
exact for simple types.

[^bidir]: J. Dunfield and N. Krishnaswami, "Bidirectional typing", ACM Computing Surveys 54(5), 2021.

**Why the extra $\textsc{Redex}$ rule.** Plain bidirectional typing cannot
infer $(\lambda x.\,b)\,a$, because the head is a lambda. The rule treats the
redex like $\mathsf{let}\ x = a\ \mathsf{in}\ b$: the argument's type is
inferred and given to the parameter. It makes terms produced by
substitution-style programming, such as $(\lambda x.\,x)\,()$, checkable
without annotations.

**Why a checking-mode $\textsc{Redex}^{\Leftarrow}$.** $\textsc{Redex}$ alone
reaches $\textsc{Sub}$ when a redex is checked, so the rest of the spine must
be inferred. When the redex returns a lambda, as in
$(\lambda x.\,\lambda y.\,y)\;()$ checked against
$\mathsf{Unit} \to \mathsf{Unit}$, that rest is the lambda $\lambda y.\,y$,
and inference fails with `CannotInferLambda` although the expected type is
known. $\textsc{Redex}^{\Leftarrow}$ passes the expected type on to the rest
of the spine instead, as checking $\mathsf{let}\ x = a\ \mathsf{in}\ b$
against $\tau$ checks $b$ against $\tau$. It accepts everything that
$\textsc{Redex}$ followed by $\textsc{Sub}$ accepts: by induction on the
spine, its last step reaches either a non-lambda head, where `check` infers
the rest of the spine as $\textsc{Redex}$ would, or a spine without
arguments, which is checked directly. Versions before the fix had only
$\textsc{Redex}$ and rejected such terms, also as arguments, as in
$f\,((\lambda x.\,\lambda y.\,y)\;())$ with
$f : (A \to A) \to A$.

### Soundness of the checker

**Theorem (soundness).** If `check(Σ, Γ, t, τ)` succeeds, then
$\Gamma \vdash t : \tau$; if `infer(Σ, Γ, t)` returns $\tau$, then
$\Gamma \vdash t : \tau$.

*Proof sketch.* Induction on the algorithmic derivation. $\textsc{Lam}$ and the
axioms map to their declarative counterparts; $\textsc{Sub}$ is immediate;
$\textsc{App}$ is $n$ uses of the declarative application rule. For
$\textsc{Redex}$ and $\textsc{Redex}^{\Leftarrow}$, write
$b' = b\{x \mapsto x'\}$. The second premise is an inference or a checking
derivation for the smaller term $b'\,a_2 \cdots a_n$, so in both cases by
induction
$\Gamma, x'{:}\sigma \vdash b'\,a_2 \cdots a_n : \tau$, and the generation
lemma for application gives types $\tau_2, \dots, \tau_n$ with
$\Gamma, x'{:}\sigma \vdash b' : \tau_2 \to \cdots \to \tau_n \to \tau$ and
$\Gamma, x'{:}\sigma \vdash a_i : \tau_i$ for $i \ge 2$. Then

$$
\begin{aligned}
&\Gamma \vdash \lambda x'.\,b' : \sigma \to \tau_2 \to \cdots \to \tau && \text{abstraction} \\
&\Gamma \vdash \lambda x.\,b : \sigma \to \tau_2 \to \cdots \to \tau && \lambda x.\,b =_\alpha \lambda x'.\,b' \\
&\Gamma \vdash (\lambda x.\,b)\,a_1 : \tau_2 \to \cdots \to \tau && \text{application, } \Gamma \vdash a_1 : \sigma \\
&\Gamma \vdash a_i : \tau_i \ (i \ge 2) && \text{strengthening, } x' \notin \mathrm{FV}(a_i) \\
&\Gamma \vdash (\lambda x.\,b)\,a_1 \cdots a_n : \tau && \text{application } (n - 1 \text{ times}).
\end{aligned}
$$

The argument does not use the mode of the second premise, so it proves both
rules; for $n = 1$ only the first three lines are needed, with $b'$ of type
$\tau$, which may be an arrow when $b'$ is a lambda. $\square$

The strengthening step is where the renaming is needed. For
$\Gamma = x{:}B$ the term

$$
(\lambda x.\,\lambda y.\,y)\;()\;x
$$

has declarative type $B$ and no other. Without the renaming, the trailing
$x$ would be typed in $\Gamma, x{:}\mathsf{Unit}$ and the checker would
answer `Unit`; versions before the fix did exactly that, and `check` accepted
the term at `Unit`. With $x' = x_1$ the trailing $x$ keeps its type $B$, and
`infer` returns $B$. $\textsc{Redex}^{\Leftarrow}$ renames in the same way, so
$(\lambda x.\,\lambda y.\,\lambda z.\,y)\;()\;x$ checks against $A \to B$ and
not against $A \to \mathsf{Unit}$.

The typed evaluator walks a spine the same way. It flattens nested `Apply`
nodes before typing the head, so the curried
$((\lambda x.\,\lambda y.\,y)\;())\;x$ is the same spine as the term above.
A lambda head cannot be inferred, so its type is rebuilt from the premises of
$\textsc{Redex}$ or $\textsc{Redex}^{\Leftarrow}$ and the expected type $\tau$ of the whole application. Write
$b' = h\,c_1 \cdots c_k$ with $h$ not an application ($k = 0$ if $b'$ is not
one). The head gets the type $\sigma \to \rho$, where $\sigma$ is inferred
for $a_1$ and $\rho$, the type of $b'$, is computed recursively: take the
head type of the flattened spine $h\,c_1 \cdots c_k\,a_2 \cdots a_n$ under
$\Gamma, x'{:}\sigma$ and remove its first $k$ domains. If that spine is
empty, $b'$ is in checking position as in $\textsc{Redex}^{\Leftarrow}$ and
$\rho = \tau$; this covers a body that is a lambda, such as $\lambda y.\,y$ in
$(\lambda x.\,\lambda y.\,y)\;()$ at $\mathsf{Unit} \to \mathsf{Unit}$. Any
other head is inferred. A redex body that consumes
the outer arguments, as in $(\lambda x.\,(\lambda y.\,\lambda z.\,z)\,x)\;()\;v$,
is therefore handled as `infer` handles it, and `normalize_eta_long` accepts
the same terms as `check`. Versions before the fix only recognised a bare
lambda head and rejected both terms with `CannotInferLambda`.

**Completeness for normal forms.** If $t$ is beta-normal and
$\Gamma \vdash t : \tau$, then `check(Σ, Γ, t, τ)` succeeds. A beta-normal
term is either a lambda, handled by $\textsc{Lam}$, or a spine whose head is a
variable, a constant or $()$; its type is determined by $\Gamma$ or $\Sigma$
and its arguments are again normal, so $\textsc{App}$ and induction apply.

Terms with redexes are accepted when every argument that the spine walk gives
to a lambda head is inferable: $a_1$ in each spine
$(\lambda x.\,b)\,a_1 \cdots a_n$, and then, recursively, the arguments that
$b\{x \mapsto x'\}\,a_2 \cdots a_n$ gives to a lambda head. This holds whether
the redex returns a lambda or not, and at every type of the term. The proof
extends the one above. An inferable term has exactly one declarative type (by
induction on the inference derivation: the head of $\textsc{App}$ and the
argument of $\textsc{Redex}$ have unique types), so a derivation of
$\Gamma \vdash (\lambda x.\,b)\,a_1 \cdots a_n : \tau$ gives the parameter the
type $\sigma$ that `infer` returns for $a_1$, and, by weakening with
$x' \notin \mathrm{FV}(a_2, \dots, a_n)$,
$\Gamma, x'{:}\sigma \vdash b\{x \mapsto x'\}\,a_2 \cdots a_n : \tau$; $\textsc{Redex}^{\Leftarrow}$
and induction on the size of the term apply. The condition is needed: both
$(\lambda f.\,f\,())\,(\lambda y.\,y)$ and
$(\lambda x.\,\lambda y.\,y)\;()\;(\lambda z.\,z)$ are typable and rejected
with `CannotInferLambda`, the second because the walk gives $\lambda z.\,z$
to the lambda head $\lambda y.\,y$.

The checker terminates. Measure a call by the size of its term, and break
ties by counting a `check` call above an `infer` call. $\textsc{Sub}$ goes
from `check` to `infer` on the same term, which lowers the measure; every
other recursive call is on a strictly smaller term ($\textsc{Redex}$ and
$\textsc{Redex}^{\Leftarrow}$ recurse
on $b\{x \mapsto x'\}\,a_2 \cdots a_n$, which lacks the binder and $a_1$;
renaming does not change the size).

### Two normalizers with different jobs

`normalize_checked` reuses the untyped normal-order beta-eta reducer of
[utlc/lambda](utlc/lambda.md) after checking the type. Its value is that it is
the *reference* semantics, with traces and step counts; it is step-bounded
only because it is shared with the untyped calculus. By strong normalization
it always ends in `NormalForm` for a large enough limit. Its normal forms are
eta-*short*.

`normalize_eta_long` is typed normalization by evaluation. It needs no limit,
and it returns the canonical representative of the $\beta\eta$ class, so two
well-typed terms are $\beta\eta$-equal iff their eta-long normal forms are
alpha-equivalent: the normalizer decides conversion.

### Beta-normal, eta-long forms

Normal forms $\mathit{Nf}^\tau$ and neutral terms $\mathit{Ne}$ are defined by
type:

$$
\begin{aligned}
\mathit{Nf}^{\sigma \to \tau} &::= \lambda x.\,\mathit{Nf}^{\tau}, &
\mathit{Nf}^{b} &::= \mathit{Ne}, &
\mathit{Nf}^{\mathsf{Unit}} &::= () \mid \mathit{Ne}, \\
\mathit{Ne} &::= x \mid c \mid \mathit{Ne}\;\mathit{Nf}^{\sigma} .
\end{aligned}
$$

Every term of arrow type is a lambda (eta-long), and every application has a
variable or a constant at its head (beta-normal). Neutral terms of type
$\mathsf{Unit}$ are kept: the eta law for the unit type ($t = ()$ for every
$t : \mathsf{Unit}$) is not implemented, so for $f : \mathsf{Unit} \to \mathsf{Unit}$
and $u : \mathsf{Unit}$ the terms $f\,u$ and $f\,()$ have different normal
forms.

### Typed normalization by evaluation

The semantic domain interprets each type:

$$
V_b = \mathit{Ne}_V, \qquad V_{\mathsf{Unit}} = \{()\} + \mathit{Ne}_V, \qquad V_{\sigma \to \tau} = \mathit{Clo}_{\sigma \to \tau} + \mathit{Ne}_V,
$$

where a closure stores a lambda body with its environment and its type, and a
semantic neutral is a free variable, a constant, or a neutral applied to a
value together with the value's type. Evaluation $\llbracket t \rrbracket\rho$
maps variables through the environment, lambdas to closures, constants to
neutrals, and applies closures by evaluating their bodies (call by value,
which is safe because evaluation of typed terms terminates). Reflection
$\uparrow^\tau$ embeds a neutral as a value; here it is the identity on
neutrals, because all eta expansion is deferred to reification. Reification
$\downarrow^\tau : V_\tau \to \mathit{Nf}^\tau$ is

$$
\begin{aligned}
\downarrow^{\sigma \to \tau} f &= \lambda x.\; \downarrow^{\tau}\big(f \cdot \uparrow^{\sigma} x\big) \qquad x \text{ fresh}, \\
\downarrow^{b} n &= \mathrm{quote}(n), \qquad
\downarrow^{\mathsf{Unit}} () = (), \qquad
\downarrow^{\mathsf{Unit}} n = \mathrm{quote}(n), \\
\mathrm{quote}(x) &= x, \quad \mathrm{quote}(c) = c, \quad \mathrm{quote}(n \cdot^{\sigma} v) = \mathrm{quote}(n)\;\downarrow^{\sigma} v,
\end{aligned}
$$

and the normal form of $\Gamma \vdash t : \tau$ is
$\downarrow^\tau \llbracket t \rrbracket \rho_\Gamma$, where $\rho_\Gamma$ maps
each $x{:}\sigma \in \Gamma$ to $\uparrow^\sigma x$. Reifying at an arrow type
applies the value to a fresh variable, which performs eta expansion; a neutral
application records the domain type of its argument so that the argument can
be reified at the right type later.[^bs]

[^bs]: U. Berger and H. Schwichtenberg, "An inverse of the evaluation functional for typed λ-calculus", LICS 1991. The type-directed presentation follows A. Abel, *Normalization by Evaluation: Dependent Types and Impredicativity*, habilitation thesis, 2013.

**Correctness (sketch).** Define a Kripke logical relation
$t \mathrel{R_\tau} d$ between terms and values, monotone under context
extension:

$$
\begin{aligned}
t \mathrel{R_b} n &\iff t =_{\beta\eta} \mathrm{quote}(n), \\
t \mathrel{R_{\mathsf{Unit}}} d &\iff t =_{\beta\eta} \downarrow^{\mathsf{Unit}} d, \\
t \mathrel{R_{\sigma \to \tau}} f &\iff \forall\, \Gamma' \supseteq \Gamma,\ s \mathrel{R_\sigma} e \implies t\,s \mathrel{R_\tau} f \cdot e .
\end{aligned}
$$

By induction on $\tau$ one proves two lemmas together: *reflection*
($t =_{\beta\eta} \mathrm{quote}(n)$ implies $t \mathrel{R_\tau} \uparrow^\tau n$)
and *reification* ($t \mathrel{R_\tau} d$ implies
$t =_{\beta\eta} \downarrow^\tau d$). The arrow case of reification is the
eta step:

$$
t \;=_\eta\; \lambda x.\,t\,x \;=_{\beta\eta}\; \lambda x.\,\downarrow^\tau (f \cdot \uparrow^\sigma x) \;=\; \downarrow^{\sigma \to \tau} f ,
$$

using $x \mathrel{R_\sigma} \uparrow^\sigma x$ (reflection) and the definition of
$R_{\sigma \to \tau}$. The *fundamental lemma* states that
$\Gamma \vdash t : \tau$ and $\gamma \mathrel{R_\Gamma} \rho$ imply
$t[\gamma] \mathrel{R_\tau} \llbracket t \rrbracket \rho$; it is proved by
induction on the typing derivation, the lambda case using that beta-reduction
is in $=_{\beta\eta}$. With $\gamma$ the identity and $\rho_\Gamma$ (related by
reflection), reification gives $t =_{\beta\eta} \mathrm{nf}(t)$ (soundness).
Completeness, that $\beta\eta$-equal terms have alpha-equivalent normal
forms, needs a second argument: a partial equivalence relation on values,
defined by induction on types like $R$, under which $\llbracket t \rrbracket$
and $\llbracket t' \rrbracket$ are related whenever $t =_{\beta\eta} t'$
(beta is function application in the model, and eta holds because
reification always expands), and related values reify to the same normal
form; Abel's thesis, cited above, gives the details. The relation $R$, read
as a computability predicate, also shows that evaluation terminates on
well-typed terms, which is why no fuel is needed.

### Fresh names in readback

Readback invents binder names with `fresh_name("x", used)`, where `used`
contains every name of the input term and context, the names in closure
environments, and the names already introduced on the path. Generated names
are therefore distinct from each other along a path and from all names of the
input, and a neutral variable is never captured by a binder introduced later.

### A bounded host stack

**Problem.** Written as host functions, the checker (`infer`, `check`, their
spine versions and the loop over the arguments of $\textsc{App}$), typed
evaluation, readback and the derived equality of types recurse once per level
of the term, of the type or of the normal form. The js, wasm and wasm-gc
stacks overflow at a depth of a few thousand, so deep binders, deep argument
positions, long curried spines, nested redexes and types nested in their
domains crashed the package (issue #13).

**Choice.** Each of the three algorithms runs as one loop over an explicit
continuation, like the untyped evaluator of [utlc/nbe](utlc/nbe.md): a
control says what to compute next, and a stack of frames in the heap holds
the rest of the callers. A call in tail position replaces the control; a
call whose result is still needed first pushes a frame for the rest of its
caller. For the checker, the controls and frames are

$$
\begin{aligned}
c \;&::=\; \mathsf{inf}(\Gamma, t) \mid \mathsf{chk}(\Gamma, t, \tau) \mid \mathsf{inf}^{*}(\Gamma, h, \vec a) \mid \mathsf{chk}^{*}(\Gamma, h, \vec a, \tau) \mid \mathsf{ret}(\tau) \mid \mathsf{ok}, \\
k \;&::=\; \mathsf{head}(\Gamma, \vec a) \mid \mathsf{arg}(\Gamma, \vec a, i, \tau) \mid \mathsf{cmp}(\tau) \mid \mathsf{redex}(\Gamma, x', b', \vec a, m), \qquad m \in \{{\Rightarrow}\} \cup \{{\Leftarrow}\,\tau\},
\end{aligned}
$$

(`CheckControl` and `CheckFrame` in the code). $\textsc{Lam}$ and the
flattening of a spine are tail calls. $\textsc{Sub}$ pushes
$\mathsf{cmp}(\tau)$ and infers; $\textsc{App}$ pushes
$\mathsf{head}(\Gamma, \vec a)$ and infers $h$, and the inferred type
$\tau_1 \to \cdots$ meeting $\mathsf{head}$ checks $a_1$ against $\tau_1$
under $\mathsf{arg}(\Gamma, \vec a, 1, \tau_2 \to \cdots)$, and so on;
$\textsc{Redex}$ and $\textsc{Redex}^{\Leftarrow}$ rename the parameter
apart, push $\mathsf{redex}(\Gamma, x', b\{x \mapsto x'\}, \vec a, m)$ and
infer $a_1$; the type $\sigma$ meeting that frame flattens
$b\{x \mapsto x'\}\,a_2 \cdots a_n$ and continues with
$\mathsf{inf}^{*}$ or $\mathsf{chk}^{*}$ under $\Gamma, x'{:}\sigma$.
Typed evaluation has controls for evaluating a term at a type, applying a
value and returning a value, and frames for the rest of a spine and for an
argument being evaluated; applying a closure to the last argument of a spine
pushes nothing, as in [utlc/nbe](utlc/nbe.md). Readback has controls for
$\downarrow^\tau$, for $\mathrm{quote}$ and for returning a term, and frames
for a binder to wrap around a body, an argument still to read back and a
function waiting for its argument. The head type of a redex spine,
defined by recursion on the remaining spine and built while returning,

$$
H(\Gamma, \lambda x.\,b, \vec a, \tau) =
\begin{cases}
\sigma \to \tau & \text{if the remaining spine is empty}, \\
\sigma \to \mathrm{drop}_{|\vec b|}\big(H(\Gamma', h', \vec b\,a_2 \cdots a_n, \tau)\big) & \text{otherwise},
\end{cases}
$$

(where $b$ flattens to $h'\,\vec b$), is computed by two loops: the first
takes the redex steps down the spine and keeps them in a heap array, the
second applies the $\sigma \to \mathrm{drop}(-)$ steps from the innermost
outwards.

*Same results, same errors.* Read a frame as the function that the rest of
its caller applies to the returned value, and a state as the stack applied to
the value of its control. Every transition is one equation of the recursive
definition, so it preserves that reading, and a run ends with the value the
recursive functions return. The machines make the calls of the definition in
its order, and no rule of the definition catches an error: every `Err`
propagates unchanged to the top. The result of the recursive functions is
therefore the first error met in that order, and the machines stop at the
same one; which `TypeError` is reported does not change.

*Equality of types.* `Ty` has a hand-written `Eq` that compares a heap array
of pending pairs, and skips a pair of physically equal types, which is sound
because the equality is reflexive.

*Linear time.* Two hidden quadratic costs would dominate at depth
$100\,000$, so they are removed without changing results. Contexts and
environments built from one another share an append-only array and read only
their own prefix, so entering $n$ binders costs $O(n)$ instead of $O(n^2)$.
Readback chooses binder names with $\operatorname{fresh}(x, U)$, the first
of the candidates $c_0 = x$, $c_1 = x\_1$, $c_2 = x\_2$, … not in $U$, and
eta-expanding at a type nested $n$ levels deep would retry the $n$ names
chosen before. It carries, with $U$, a position $p$ such that every $c_q$
with $q < p$ is in $U$, and starts the search there. If $c_{p'}$ is chosen,
every $c_q$ with $q \le p'$ is in $U \cup \{c_{p'}\}$, so $p' + 1$ is a valid
position for the extended set; readback only ever adds names to $U$, so the
position stays valid along the path, and the name found is the one
$\operatorname{fresh}$ returns.

## Correctness and invariants

- `check` and `infer` terminate; on success, the term is declaratively typable
  at the reported type (soundness theorem). The regression tests include
  redexes whose parameter occurs free in a trailing argument.
- `check` accepts every well-typed beta-normal term, and every well-typed
  term in which each argument given to a lambda head is inferable, including
  redexes that return a lambda.
- `normalize_eta_long` returns `Ok` exactly for terms that `check` accepts;
  its result is in
  $\mathit{Nf}^\tau$, is $\beta\eta$-equal to the input, and is the same (up to
  $=_\alpha$) for $\beta\eta$-equal inputs.
- `normalize_checked` returns `Err` before any reduction for ill-typed input.
- `NormalizationError` signals a violated internal invariant and is not
  produced for checked input.
- `check`, `infer`, `normalize_checked`, `normalize_eta_long` and `==` on
  types use a constant host stack depth; terms and types nested 100 000
  levels deep are handled on every backend (`src/stlc/deep_test.mbt`).

The tests in `src/stlc/stlc_test.mbt` cover typing and rejection, shadowing,
eta expansion of open variables and of constants (including nested arrow
types and higher-order arguments), agreement of the two normalizers on
small terms, and agreement of `check` and `normalize_eta_long` on redexes with
curried heads, mixed flat and nested spines, and bodies that consume the outer
arguments. They also cover redexes checked against an arrow
($\textsc{Redex}^{\Leftarrow}$): redexes that return a lambda, alone and as
arguments, in curried and flat spines, nested ones, the renaming shape above
in checking mode, and ill-typed variants that are still rejected.

## Alternatives rejected

- **Church-style annotated lambdas.** Annotations would make inference
  complete but change the shared `Term` syntax; the bidirectional checker keeps
  terms unannotated.
- **Hindley–Milner inference.** Unification would infer types of unannotated
  lambdas, but polymorphism and type variables are beyond this calculus.
- **Fuel for typed NbE.** Unnecessary by strong normalization; the untyped
  [utlc/nbe](utlc/nbe.md) keeps fuel because it needs it.
- **Eta for the unit type.** Implementable by reifying every neutral of type
  $\mathsf{Unit}$ as $()$; not done, so that neutrals stay observable. The
  decided equality is $\beta\eta$ for arrows only.

## Boundaries

- Types are $b$, $\mathsf{Unit}$ and arrows: no products, sums, polymorphism or
  dependent types.
- No unit eta; normal forms are eta-long for arrow types only.
- Constants are opaque: there are no delta rules.
- `normalize_checked` is bounded by a step limit because it reuses the untyped
  reducer.
- `normalize_eta_long` is stack-safe but takes time quadratic in the depth of
  redexes and applications nested in argument positions: typed evaluation
  checks each argument again before evaluating it, and infers the first
  argument of each redex again to type its head.
- `Debug` of a deep term, type or error recurses and can overflow the stack.
