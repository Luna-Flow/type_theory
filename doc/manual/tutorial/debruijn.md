# debruijn tutorial

This tutorial converts named lambda terms to De Bruijn form, uses that form
to compare terms and to reduce them without renaming, validates untrusted
nameless input, and converts results back to names for display.

| I want to | Use |
| --- | --- |
| convert a named term to indices | `from_named` |
| convert back with readable names | `to_named` |
| check that every index has a binder | `validate` |
| reduce without renaming | `reduce_once`, `normalize` |
| open a binder with an argument | `instantiate` |
| move a term under binders | `shift` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.3.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/rewrite",
  "Luna-Flow/type_theory/debruijn",
}
```

$\lambda x.\,\lambda y.\,x$ becomes $\lambda.\,\lambda.\,1$: the variable
refers to the binder one level further out.

```moonbit
test "quick start: the K combinator without names" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let k : @syntax.Term[Int] = Bind(x, Bind(y, Variable(x)))
  assert_eq(@debruijn.from_named(k), Bind(Bind(Bound(1))))
}
```

## Everyday tasks

### Compare terms up to bound names

Alpha-equivalent named terms have equal De Bruijn forms, so `==` after
conversion decides alpha-equivalence:

```moonbit
test "alpha-equivalence by conversion" {
  let a : @syntax.Term[Int] = Bind(@core.Name::new("p"), Variable(@core.Name::new("p")))
  let b : @syntax.Term[Int] = Bind(@core.Name::new("q"), Variable(@core.Name::new("q")))
  assert_eq(@debruijn.from_named(a), @debruijn.from_named(b))
}
```

`@syntax.alpha_equal` gives the same answer without building the converted
terms; the conversion pays off when you keep the nameless form for further
work.

### Reduce without renaming

Beta reduction on nameless terms shifts indices instead of renaming binders.
The classic capture example $(\lambda x.\,\lambda y.\,x)\,y$ needs no fresh
name:

```moonbit
test "beta without capture problems" {
  let y = @core.Name::new("y")
  let term : @debruijn.DbTerm[Int] = Apply(Bind(Bind(Bound(1))), [Free(y)])
  assert_eq(
    @debruijn.normalize(term, 10),
    NormalForm(term=Bind(Free(y)), steps=1),
  )
}
```

The free `y` stays free because it is a name, and the inner binder needs no
new name because it has none.

### Validate untrusted input

Terms built by hand or read from outside can contain indices that point past
every binder. Check them before reducing:

```moonbit
test "reject a dangling index" {
  let bad : @debruijn.DbTerm[Int] = Bind(Apply(Bound(0), [Bound(2)]))
  match @debruijn.validate(bad) {
    Err(UnboundIndex(index~, depth~)) => {
      assert_eq(index, 2)
      assert_eq(depth, 1)
    }
    _ => fail("expected an unbound index")
  }
}
```

### Convert back to names for display

`to_named` names binders `x`, `x_1`, … and avoids the free names of the term:

```moonbit
test "readable names come back" {
  let x = @core.Name::new("x")
  let term : @debruijn.DbTerm[Int] = Bind(Bind(Apply(Bound(1), [Free(x)])))
  match @debruijn.to_named(term) {
    Ok(Bind(outer, Bind(inner, _))) => {
      inspect(outer.text(), content="x_1")
      inspect(inner.text(), content="x_2")
    }
    _ => fail("well scoped")
  }
}
```

The binders skip `x` because `x` is free in the term.

### Open a binder by hand

`instantiate(body, arg)` is the result of $(\lambda.\,body)\,arg$. Use it when
you implement your own reducer or evaluator:

```moonbit
test "open a binder" {
  // body of λ. (λ. 1 0): the outer variable applied to the inner one
  let body : @debruijn.DbTerm[Int] = Bind(Apply(Bound(1), [Bound(0)]))
  assert_eq(
    @debruijn.instantiate(body, Value(9)),
    Ok(Bind(Apply(Value(9), [Bound(0)]))),
  )
}
```

## Going further

### Check the named reducer against the nameless one

Because the conversion commutes with beta reduction, the named and nameless
reducers must agree up to alpha-equivalence. This is a good property test for
any reducer you write:

```moonbit
fn named_beta(t : @syntax.Term[Int]) -> @syntax.Term[Int]? {
  match t {
    Apply(Bind(x, body), [arg]) =>
      Some(@substitution.Substitution::singleton(x, arg).apply(body))
    _ => None
  }
}

test "named and nameless beta agree" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let named : @syntax.Term[Int] = Apply(Bind(x, Bind(y, Apply(Variable(x), [Variable(y)]))), [
    Variable(y),
  ])
  match (named_beta(named), @debruijn.reduce_once(@debruijn.from_named(named))) {
    (Some(n), Reduced(after~, ..)) => assert_eq(@debruijn.from_named(n), after)
    _ => fail("both reduce")
  }
}
```

(This example also imports `Luna-Flow/type_theory/substitution`.)

### Fast normalization

`normalize` repeats one search-and-contract step from the root, which is
simple and traceable but slow on long reductions. For large untyped terms use
[utlc/nbe](utlc/nbe.md), which works on the same `DbTerm` and returns the same
normal forms (up to the shape of application spines).

## Common pitfalls

- **Counting indices from the outside.** `Bound(0)` is the *innermost*
  binder. $\lambda x.\,\lambda y.\,x$ is `Bind(Bind(Bound(1)))`, not
  `Bound(0)`.
- **Reducing unvalidated terms.** `reduce_once` and `substitute_bound` do not
  detect unbound indices. Call `validate` first on input you did not build
  with `from_named`.
- **Expecting binder names to survive.** `to_named(from_named(t))` is
  alpha-equivalent to `t`, but binder names are regenerated.
- **Spines.** `Apply(f, [a, b])` and `Apply(Apply(f, [a]), [b])` mean the same
  application but are different values; normalize them to one shape before
  comparing with `==`.

## Next steps

- [debruijn API](../api/debruijn.md) for every function and error case.
- [debruijn design](../design/debruijn.md) for shifting, instantiation and the
  correctness lemmas.
- [utlc/nbe tutorial](utlc/nbe.md) for normalization by evaluation on
  `DbTerm`.
