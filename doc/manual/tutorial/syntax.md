# syntax tutorial

This tutorial builds terms with binders using `Term[T]`, prints them, asks
which variables are free, compares terms up to the names of bound variables
and renames variables without capture. At the end you write an analysis that
works for any AST implementing `BindingSyntax`.

| I want to | Use |
| --- | --- |
| build a term with binders | the constructors of `@syntax.Term` |
| list the free variables, or every name | `free_variables`, `all_names` |
| compare terms up to bound names | `alpha_equal` |
| rename free variables without capture | `Term::rename_free` |
| change the type of the constants | `Term::map_values` |
| write one analysis for every binding-aware AST | functions bounded by `BindingSyntax` |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.2.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
}
```

The identity function $\lambda x.\,x$ has no free variables; $\lambda x.\,y$
has one:

```moonbit
test "quick start: free variables" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let id : @syntax.Term[Int] = Bind(x, Variable(x))
  let k : @syntax.Term[Int] = Bind(x, Variable(y))
  assert_eq(@syntax.free_variables(id).length(), 0)
  assert_true(@syntax.free_variables(k).contains(y))
}
```

## Everyday tasks

### Build terms with small helpers

Writing `@core.Name::new` everywhere gets noisy. Define helpers once:

```moonbit
fn v(name : String) -> @syntax.Term[Int] {
  @syntax.Variable(@core.Name::new(name))
}

fn lam(name : String, body : @syntax.Term[Int]) -> @syntax.Term[Int] {
  @syntax.Bind(@core.Name::new(name), body)
}

fn app(f : @syntax.Term[Int], args : Array[@syntax.Term[Int]]) -> @syntax.Term[Int] {
  @syntax.Apply(f, args)
}

test "the K combinator" {
  let k = lam("x", lam("y", v("x")))
  assert_true(k is Bind(_, Bind(_, Variable(_))))
  assert_eq(app(k, [v("a")]), @syntax.Apply(k, [v("a")]))
}
```

### Print a term

`Term` has no text format of its own, because the right notation depends on
the language it encodes. A printer for lambda notation is a short recursive
function:

```moonbit
fn show(t : @syntax.Term[Int]) -> String {
  match t {
    Value(n) => n.to_string()
    Variable(x) => x.text()
    Apply(f, args) => {
      let parts = [show(f), ..args.map(show)]
      "(" + parts.join(" ") + ")"
    }
    Bind(x, body) => "λ" + x.text() + ". " + show(body)
  }
}

test "print λf. f 1" {
  let f = @core.Name::new("f")
  let t : @syntax.Term[Int] = Bind(f, Apply(Variable(f), [Value(1)]))
  inspect(show(t), content="λf. (f 1)")
}
```

### Compare terms up to bound names

`==` compares terms literally. `alpha_equal` ignores the names of bound
variables, which is almost always what you want:

```moonbit
test "λx. x and λy. y" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let a : @syntax.Term[Int] = Bind(x, Variable(x))
  let b : @syntax.Term[Int] = Bind(y, Variable(y))
  assert_false(a == b)
  assert_true(@syntax.alpha_equal(a, b))
}
```

### Rename free variables safely

Renaming `x` to `y` in $\lambda y.\,x$ must not produce $\lambda y.\,y$.
`rename_free` renames the binder first:

```moonbit
test "renaming avoids capture" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let t : @syntax.Term[Int] = Bind(y, Apply(Variable(x), [Variable(y)]))
  let r = t.rename_free(@core.Renaming::singleton(x, y))
  let y1 = @core.Name::new("y_1")
  let expected : @syntax.Term[Int] = Bind(y1, Apply(Variable(y), [Variable(y1)]))
  assert_eq(r, expected)
}
```

The free `x` became `y`, and the binder became `y_1` so that the new `y`
stays free.

### Change the type of the constants

`map_values` converts constants and leaves the binding structure alone. Here
integer literals become floating-point literals:

```moonbit
test "map Int constants to Double" {
  let x = @core.Name::new("x")
  let t : @syntax.Term[Int] = Bind(x, Apply(Variable(x), [Value(2)]))
  let d : @syntax.Term[Double] = t.map_values(n => n.to_double())
  assert_true(d is Bind(_, Apply(_, [Value(2.0)])))
}
```

## Going further

### Write an analysis for every binding-aware AST

Functions written against `BindingSyntax` work for `Term[T]` and for any
downstream AST that implements the trait. This one counts binders:

```moonbit
fn[N : @syntax.BindingSyntax] count_binders(node : N) -> Int {
  match @syntax.BindingSyntax::project(node) {
    Opaque | Variable(_) => 0
    Apply(head, args) =>
      args.fold(init=count_binders(head), (acc, a) => acc + count_binders(a))
    Bind(_, body) => 1 + count_binders(body)
  }
}

test "count binders generically" {
  let x = @core.Name::new("x")
  let t : @syntax.Term[Int] = Bind(x, Apply(Bind(x, Variable(x)), [Value(0)]))
  assert_eq(count_binders(t), 2)
}
```

The [adapter tutorial](adapter.md) implements `BindingSyntax` for a custom
AST, after which `count_binders`, generic substitution and generic rewriting
all apply to it.

### Rename a binder by hand

When you build a binder from parts, `alpha_rename_bound` changes the name of
its variable, and refuses a name that is already used in the body:

```moonbit
test "rename the variable of a binder" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let body : @syntax.Term[Int] = Apply(Variable(x), [Variable(y)])
  assert_true(body.alpha_rename_bound(x, y) is None)
  match body.alpha_rename_bound(x, z) {
    Some(renamed) => {
      let before : @syntax.Term[Int] = Bind(x, body)
      let after : @syntax.Term[Int] = Bind(z, renamed)
      assert_true(@syntax.alpha_equal(before, after))
    }
    None => fail("z is unused")
  }
}
```

## Common pitfalls

- **`==` is not alpha-equivalence.** Results of substitution and
  normalization may have renamed binders such as `y_1`. Compare them with
  `alpha_equal`.
- **Payloads are compared with their own `==`.** `alpha_equal` inherits it:
  with `Term[Double]`, a term containing `Value(0.0 / 0.0)` (NaN) is not
  alpha-equal to itself, and `Value(0.0)` equals `Value(-0.0)`.
- **Variables inside values.** `Value(T)` is never inspected. If your
  constants contain variables, implement `BindingSyntax` for your AST instead
  of wrapping it in `Term`.
- **Calling `alpha_rename_bound` on the binder.** It expects the *body*:
  `body.alpha_rename_bound(x, z)`, not `Bind(x, body).alpha_rename_bound(...)`,
  which would find no free `x` to rename.
- **Method-style trait calls.** `term.project()` is deprecated; write
  `@syntax.BindingSyntax::project(term)`.

## Next steps

- [syntax API](../api/syntax.md): every function and its contract.
- [syntax design](../design/syntax.md): the definitions and the proofs behind
  alpha-equivalence and capture-avoiding renaming.
- [substitution tutorial](substitution.md): replacing variables by terms.
