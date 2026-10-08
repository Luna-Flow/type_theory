# stlc design

## Design goal

`stlc` is a small, complete instance of a typed calculus on the shared
substrate: it reuses the named syntax, substitution, rewriting and the
untyped reducer, and adds what types make possible: a decidable type checker
and a normalizer that needs no step limit and returns canonical
(beta-normal, eta-long) forms. It is the model for richer typed cores built on
`type_theory`.

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
\frac{\Gamma \vdash a_1 \Rightarrow \sigma \qquad \Gamma, x{:}\sigma \vdash b\,a_2 \cdots a_n \Rightarrow \tau}
     {\Gamma \vdash (\lambda x.\,b)\,a_1\,a_2 \cdots a_n \Rightarrow \tau}
\qquad
\textsc{Lam}\;
\frac{\Gamma, x{:}\sigma \vdash b \Leftarrow \tau}{\Gamma \vdash \lambda x.\,b \Leftarrow \sigma \to \tau}
\qquad
\textsc{Sub}\;
\frac{\Gamma \vdash t \Rightarrow \tau' \qquad \tau' = \tau}{\Gamma \vdash t \Leftarrow \tau}
$$

In $\textsc{App}$ the spine is flattened first, so nested `Apply` nodes are one
application $h\,a_1 \cdots a_n$; if $h$ has fewer arrows than arguments the
result is `ExpectedFunction`. In $\textsc{Redex}$ with $n = 1$ the second
premise is $\Gamma, x{:}\sigma \vdash b \Rightarrow \tau$. $\textsc{Sub}$
applies to every term except a lambda checked against an arrow; a lambda in
inference position fails with `CannotInferLambda`. Type equality in
$\textsc{Sub}$ is syntactic, which is exact for simple types.

[^bidir]: J. Dunfield and N. Krishnaswami, "Bidirectional typing", ACM Computing Surveys 54(5), 2021.

**Why the extra $\textsc{Redex}$ rule.** Plain bidirectional typing cannot
infer $(\lambda x.\,b)\,a$, because the head is a lambda. The rule treats the
redex like $\mathsf{let}\ x = a\ \mathsf{in}\ b$: the argument's type is
inferred and given to the parameter. It makes terms produced by
substitution-style programming, such as $(\lambda x.\,x)\,()$, checkable
without annotations.

### Soundness of the checker

**Theorem.** If `check(Σ, Γ, t, τ)` succeeds, then $\Gamma \vdash t : \tau$;
if `infer(Σ, Γ, t)` returns $\tau$, then $\Gamma \vdash t : \tau$ — provided
every use of $\textsc{Redex}$ satisfies $x \notin \mathrm{FV}(a_2, \dots, a_n)$.

*Proof sketch.* Induction on the algorithmic derivation. $\textsc{Lam}$ and the
axioms map to their declarative counterparts; $\textsc{Sub}$ is immediate;
$\textsc{App}$ is $n$ uses of the declarative application rule. For
$\textsc{Redex}$, invert the second premise: $\Gamma, x{:}\sigma \vdash b \Rightarrow \tau_2 \to \cdots \to \tau_n \to \tau$
and $\Gamma, x{:}\sigma \vdash a_i : \tau_i$ for $i \ge 2$. Then

$$
\begin{aligned}
&\Gamma \vdash \lambda x.\,b : \sigma \to \tau_2 \to \cdots \to \tau && \text{abstraction} \\
&\Gamma \vdash (\lambda x.\,b)\,a_1 : \tau_2 \to \cdots \to \tau && \text{application, } \Gamma \vdash a_1 : \sigma \\
&\Gamma \vdash a_i : \tau_i \ (i \ge 2) && \text{strengthening, needs } x \notin \mathrm{FV}(a_i) \\
&\Gamma \vdash (\lambda x.\,b)\,a_1 \cdots a_n : \tau && \text{application } (n - 1 \text{ times}).
\end{aligned}
$$

$\square$

The strengthening step is where the side condition is used, and the
implementation does not enforce it: for $\Gamma = x{:}B$,

$$
(\lambda x.\,\lambda y.\,y)\;()\;x
$$

has declarative type $B$ (the outer $x$ has type $B$), but `infer` types the
second argument in $\Gamma, x{:}\mathsf{Unit}$ and returns `Unit`.
`normalize_eta_long` then rejects the term at either type, because its
evaluator checks the arguments in the original context. This is a known issue
of the current implementation (recorded in the correctness checklist);
renaming the parameter apart from the free variables of the remaining
arguments avoids it.

**Completeness for normal forms.** If $t$ is beta-normal and
$\Gamma \vdash t : \tau$, then `check(Σ, Γ, t, τ)` succeeds. A beta-normal
term is either a lambda, handled by $\textsc{Lam}$, or a spine whose head is a
variable, a constant or $()$; its type is determined by $\Gamma$ or $\Sigma$
and its arguments are again normal, so $\textsc{App}$ and induction apply.
Terms with redexes are accepted when each redex's first argument is
inferable; $(\lambda f.\,f\,())\,(\lambda y.\,y)$ is rejected with
`CannotInferLambda` although it is typable.

The checker terminates: every recursive call is on a strictly smaller term
($\textsc{Redex}$ recurses on $b\,a_2 \cdots a_n$, which is smaller than the
redex).

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
Since evaluation identifies $\beta\eta$-equal terms (beta is function
application in the model, eta holds because reification always expands), equal
terms have equal normal forms (completeness). The same relation, read as a
computability predicate, shows that evaluation terminates on well-typed
terms, which is why no fuel is needed.

### Fresh names in readback

Readback invents binder names with `fresh_name("x", used)`, where `used`
contains every name of the input term and context, the names in closure
environments, and the names already introduced on the path. Generated names
are therefore distinct from each other along a path and from all names of the
input, and a neutral variable is never captured by a binder introduced later.

## Correctness / invariants

- `check` and `infer` terminate; on success, the term is declaratively typable
  at the reported type, subject to the side condition of $\textsc{Redex}$ (see
  the known issue above).
- `check` accepts every well-typed beta-normal term.
- `normalize_eta_long` returns `Ok` exactly for terms that `check` accepts,
  except for the known issue; its result is in
  $\mathit{Nf}^\tau$, is $\beta\eta$-equal to the input, and is the same (up to
  $=_\alpha$) for $\beta\eta$-equal inputs.
- `normalize_checked` returns `Err` before any reduction for ill-typed input.
- `NormalizationError` signals a violated internal invariant and is not
  produced for checked input.

The tests in `src/stlc/stlc_test.mbt` cover typing and rejection, shadowing,
eta expansion of open variables and of constants (including nested arrow
types and higher-order arguments), and agreement of the two normalizers on
small terms.

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
- The $\textsc{Redex}$ rule does not rename its parameter apart from later
  arguments (known issue).
- `normalize_checked` is bounded by a step limit because it reuses the untyped
  reducer.
