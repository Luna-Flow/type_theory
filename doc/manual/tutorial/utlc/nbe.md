# utlc/nbe tutorial

This tutorial normalizes untyped lambda terms with normalization by
evaluation: fast normal forms of De Bruijn terms within a fuel budget. You will
normalize terms written with names, pick a budget, read the `consumed`
counter, and compare results with the small-step reducer.

| I want to | Use |
| --- | --- |
| normalize a De Bruijn term quickly | `@nbe.normalize(term, fuel)` |
| normalize a named term | `@debruijn.from_named`, then `normalize`, then `@debruijn.to_named` |
| bound the work on a term that may diverge | the fuel argument and `FuelExhausted` |
| evaluate once and read back later | `eval`, then `quote` |
| read back a free variable | `reflect_free` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/debruijn",
  "Luna-Flow/type_theory/utlc/nbe",
}
```

```moonbit
test "quick start: (λ. 0) 5" {
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Bound(0)), [Value(5)])
  match @nbe.normalize(term, 100) {
    NormalForm(term=normal, consumed~) => {
      assert_eq(normal, Value(5))
      assert_true(consumed > 0)
    }
    _ => fail("small closed term")
  }
}
```

## Everyday tasks

### Normalize a named term

Write terms with names, convert them with `from_named`, normalize, and
convert back for display:

```moonbit
fn church(n : Int) -> @syntax.Term[Int] {
  let f = @core.Name::new("f")
  let x = @core.Name::new("x")
  let mut body : @syntax.Term[Int] = Variable(x)
  for _ in 0..<n {
    body = Apply(Variable(f), [body])
  }
  Bind(f, Bind(x, body))
}

test "2 * 3 = 6 with Church numerals" {
  let m = @core.Name::new("m")
  let n = @core.Name::new("n")
  let f = @core.Name::new("f")
  // times = λm. λn. λf. m (n f)
  let times : @syntax.Term[Int] = Bind(
    m,
    Bind(n, Bind(f, Apply(Variable(m), [Apply(Variable(n), [Variable(f)])]))),
  )
  let term : @syntax.Term[Int] = Apply(times, [church(2), church(3)])
  match @nbe.normalize(@debruijn.from_named(term), 10_000) {
    NormalForm(term=normal, ..) => assert_eq(normal, @debruijn.from_named(church(6)))
    _ => fail("normalizes")
  }
}
```

Comparing De Bruijn forms with `==` is comparing up to alpha-equivalence.

### Choose a fuel budget

Fuel bounds the work, not the time. Too little fuel gives `FuelExhausted`;
the `consumed` value of a successful run is the exact amount that run needs:

```moonbit
test "the budget a run needs" {
  let id : @debruijn.DbTerm[Int] = Bind(Bound(0))
  let term : @debruijn.DbTerm[Int] = Apply(id, [Apply(id, [Value(1)])])
  match @nbe.normalize(term, 1000) {
    NormalForm(consumed~, ..) => {
      assert_true(@nbe.normalize(term, consumed) is NormalForm(..))
      assert_true(@nbe.normalize(term, consumed - 1) is FuelExhausted(..))
    }
    _ => fail("normalizes")
  }
}
```

### Recognise divergence and laziness

$\Omega$ never reaches a normal form, so it always exhausts the budget. An
argument that is never used is never evaluated, so passing $\Omega$ to a
constant function is fine:

```moonbit
test "omega and a lazy argument" {
  let w : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(0)]))
  let omega : @debruijn.DbTerm[Int] = Apply(w, [w])
  assert_true(@nbe.normalize(omega, 500) is FuelExhausted(consumed=500))
  let ignore : @debruijn.DbTerm[Int] = Bind(Value(0))
  assert_true(@nbe.normalize(Apply(ignore, [omega]), 500) is NormalForm(term=Value(0), ..))
}
```

### Reject ill-scoped input

`normalize` validates first and reports a dangling index as data:

```moonbit
test "scope errors are reported" {
  let bad : @debruijn.DbTerm[Int] = Bind(Bound(3))
  assert_eq(
    @nbe.normalize(bad, 100),
    ScopeFailure(error=UnboundIndex(index=3, depth=1), consumed=0),
  )
}
```

## Going further

### Compare with small-step reduction

NbE returns unary applications; `@debruijn.normalize` keeps n-ary spines.
Flatten spines before comparing:

```moonbit
fn flatten(t : @debruijn.DbTerm[Int]) -> @debruijn.DbTerm[Int] {
  match t {
    Apply(head, args) => {
      let flat_args = args.map(flatten)
      match flatten(head) {
        Apply(h, inner) => Apply(h, [..inner, ..flat_args])
        h => Apply(h, flat_args)
      }
    }
    Bind(body) => Bind(flatten(body))
    other => other
  }
}

test "nbe agrees with small-step after flattening" {
  let f = @core.Name::new("f")
  // (λ. λ. f 1 0) 7 8
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Bind(Apply(Free(f), [Bound(1), Bound(0)]))), [
    Value(7),
    Value(8),
  ])
  match (@nbe.normalize(term, 1000), @debruijn.normalize(term, 100)) {
    (NormalForm(term=a, ..), NormalForm(term=b, ..)) => {
      assert_false(a == b)
      assert_eq(flatten(a), flatten(b))
    }
    _ => fail("both normalize")
  }
}
```

### Use the pipeline directly

`eval` produces an opaque semantic value; `quote` reads it back. Splitting the
two is useful to evaluate once and quote at a chosen level, or to quote
neutral values made with `reflect_free`:

```moonbit
test "eval and quote separately" {
  let k : @debruijn.DbTerm[Int] = Bind(Bind(Bound(1)))
  match @nbe.eval(k, 100) {
    Evaluated(value~, ..) =>
      assert_true(@nbe.quote(value, 0, 100) is Quoted(term=Bind(Bind(Bound(1))), ..))
    _ => fail("closed term")
  }
}
```

## Common pitfalls

- **Comparing with the small-step result by `==`.** Spine shapes differ;
  flatten first.
- **Treating `FuelExhausted` as divergence.** It only says the budget ran
  out. Raise the budget or use the typed [stlc](../stlc.md) normalizer, which
  needs no budget.
- **Duplicated arguments.** Evaluation is call by name without sharing; a
  term that uses an expensive argument many times pays for it each time.
- **Open terms with dangling indices.** Free variables must be `Free(name)`;
  a `Bound` index without a binder is a scope error.

## Next steps

- [utlc/nbe API](../../api/utlc/nbe.md) for every type and function.
- [utlc/nbe design](../../design/utlc/nbe.md) for the semantic domain and the
  soundness argument.
- [stlc tutorial](../stlc.md) for typed, eta-long NbE.
