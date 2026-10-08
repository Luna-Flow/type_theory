# utlc/lambda tutorial

This tutorial computes with the untyped lambda calculus: it builds terms,
normalizes them with beta and eta, encodes booleans and numbers as functions,
and deals with terms that never stop reducing.

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```text
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/utlc/lambda",
}
```

```moonbit
test "quick start: (λx. x) 1" {
  let x = @core.Name::new("x")
  let id : @syntax.Term[Int] = @lambda.abstraction(x, Variable(x))
  let term = @lambda.application(id, Value(1))
  assert_eq(@lambda.normalize(term, 10), NormalForm(term=Value(1), steps=1))
}
```

## Everyday tasks

The tasks use a few helpers to keep terms short:

```moonbit
fn lv(s : String) -> @syntax.Term[Int] {
  @syntax.Term::Variable(@core.Name::new(s))
}

fn lam(s : String, body : @syntax.Term[Int]) -> @syntax.Term[Int] {
  @lambda.abstraction(@core.Name::new(s), body)
}

fn ap(f : @syntax.Term[Int], a : @syntax.Term[Int]) -> @syntax.Term[Int] {
  @lambda.application(f, a)
}

fn nf(t : @syntax.Term[Int]) -> @syntax.Term[Int] {
  match @lambda.normalize(t, 1000) {
    NormalForm(term~, ..) => term
    StepLimitReached(..) => abort("no normal form within 1000 steps")
  }
}
```

### Encode booleans

Church booleans choose between two arguments:
$\mathsf{true} = \lambda t.\,\lambda f.\,t$, $\mathsf{false} = \lambda t.\,\lambda f.\,f$,
and $\mathsf{if}\;b\;x\;y = b\,x\,y$.

```moonbit
test "church booleans" {
  let tru = lam("t", lam("f", lv("t")))
  let fls = lam("t", lam("f", lv("f")))
  let not_ = lam("b", ap(ap(lv("b"), fls), tru))
  assert_true(@syntax.alpha_equal(nf(ap(not_, tru)), fls))
  assert_true(@syntax.alpha_equal(nf(ap(not_, fls)), tru))
}
```

### Encode numbers and add them

The Church numeral $n$ applies a function $n$ times:
$\overline{2} = \lambda f.\,\lambda x.\,f\,(f\,x)$. Addition is
$\lambda m.\,\lambda n.\,\lambda f.\,\lambda x.\,m\,f\,(n\,f\,x)$.

```moonbit
fn numeral(n : Int) -> @syntax.Term[Int] {
  let mut body = lv("x")
  for _ in 0..<n {
    body = ap(lv("f"), body)
  }
  lam("f", lam("x", body))
}

test "2 + 2 = 4" {
  let plus = lam(
    "m",
    lam("n", lam("f", lam("x", ap(ap(lv("m"), lv("f")), ap(ap(lv("n"), lv("f")), lv("x")))))),
  )
  let four = nf(ap(ap(plus, numeral(2)), numeral(2)))
  assert_true(@syntax.alpha_equal(four, numeral(4)))
}
```

Normal forms may use different binder names (`f_1`, …) from your
expectation; `alpha_equal` ignores them.

### Use eta to simplify wrappers

$\lambda x.\,g\,x$ is just $g$ when $x$ is not free in $g$. `normalize`
removes such wrappers:

```moonbit
test "eta removes a wrapper" {
  let wrapped = lam("x", ap(lv("g"), lv("x")))
  assert_eq(@lambda.normalize(wrapped, 10), NormalForm(term=lv("g"), steps=1))
  let not_a_wrapper = lam("x", ap(lv("x"), lv("x")))
  assert_eq(
    @lambda.normalize(not_a_wrapper, 10),
    NormalForm(term=not_a_wrapper, steps=0),
  )
}
```

### Handle terms that do not terminate

$\Omega = (\lambda w.\,w\,w)(\lambda w.\,w\,w)$ reduces to itself forever.
The step limit turns that into a result you can test for:

```moonbit
test "omega hits the step limit" {
  let self_apply = lam("w", ap(lv("w"), lv("w")))
  let omega = ap(self_apply, self_apply)
  match @lambda.normalize(omega, 50) {
    StepLimitReached(steps~, ..) => assert_eq(steps, 50)
    NormalForm(..) => fail("omega has no normal form")
  }
  // a discarded omega is harmless under normal order
  assert_eq(nf(ap(lam("x", lv("y")), omega)), lv("y"))
}
```

## Going further

### Only beta, or another strategy

`normalize` fixes beta-eta and normal order. For other combinations, pass a
rule and a strategy to `@eval.evaluate` (import `Luna-Flow/type_theory/eval`):

```moonbit
test "beta only, weak head" {
  let term = ap(lam("x", lam("y", ap(lv("x"), lv("y")))), lv("g"))
  let rule = @rewrite.RuleName::unsafe_new("beta")
  match @eval.evaluate(term, rule, @lambda.beta_rule, WeakHead, 10) {
    NormalForm(term=result, steps~) => {
      assert_eq(steps, 1)
      assert_true(@syntax.alpha_equal(result, lam("y", ap(lv("g"), lv("y")))))
    }
    StepLimitReached(..) => fail("one step")
  }
}
```

Beta alone under weak head stops at $\lambda y.\,g\,y$; `normalize` would
also eta-reduce it to $g$.

### Domain values

`Value(v)` is a constant that never reduces and is copied by substitution.
Add reduction rules for constants (such as arithmetic on `Value(Int)`) with
your own rule, and combine it with `beta_rule` as shown in the
[rewrite tutorial](../rewrite.md).

### Faster normalization

Normal-order reduction on named terms renames binders and repeats searches
from the root. For large terms, convert with `@debruijn.from_named` and use
[utlc/nbe](nbe.md).

## Common pitfalls

- **n-ary applications and eta.** `Apply(f, [a, x])` under `Bind(x, …)` is
  not eta-reduced; build applications with `application` (unary) if you rely
  on eta.
- **Comparing with `==`.** Beta renames binders to avoid capture; use
  `@syntax.alpha_equal`.
- **Reading `StepLimitReached` as divergence.** It only means the limit was
  reached. Normalizing terms can need many steps.
- **Expecting constants to compute.** `Value(1)` applied to anything stays
  stuck; the calculus has no built-in arithmetic.

## Next steps

- [utlc/lambda API](../../api/utlc/lambda.md) for the exact contracts.
- [utlc/lambda design](../../design/utlc/lambda.md) for beta, eta and the
  classical theorems.
- [stlc tutorial](../stlc.md) for the typed calculus, where every term
  normalizes.
