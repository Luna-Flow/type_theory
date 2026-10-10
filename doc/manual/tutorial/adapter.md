# adapter tutorial

This tutorial connects your own expression type to `type_theory`. You
implement `@syntax.BindingSyntax` for a small AST and then use generic free
variables, capture-avoiding substitution and rewriting on it, without
converting to `Term[T]`. Finally you test the adapter laws.

| I want to | Use |
| --- | --- |
| connect my AST to the library | `impl @syntax.BindingSyntax for MyAst` |
| find free variables in my AST | `@syntax.generic_free_variables` |
| substitute without capture | `@substitution.GenericSubstitution::apply_once` |
| simplify with my own rules | `@rewrite.generic_top_down_once`, `generic_normalize` |
| test that my adapter is lawful | the view-law tests under "Going further" |

## Quick start

```bash
moon add Luna-Flow/type_theory@0.3.0
```

```moonbit nocheck
import {
  "Luna-Flow/type_theory/core",
  "Luna-Flow/type_theory/syntax",
  "Luna-Flow/type_theory/substitution",
  "Luna-Flow/type_theory/rewrite",
}
```

Here is an expression language with numbers, operator symbols, variables,
calls and a binder `Fun(x, body)`, and its adapter:

```moonbit
priv enum Expr {
  Num(Int)
  Sym(String)
  Var(@core.Name)
  Call(Expr, Array[Expr])
  Fun(@core.Name, Expr)
} derive(Eq, Debug)

impl @syntax.BindingSyntax for Expr with fn project(self) {
  match self {
    Num(_) | Sym(_) => Opaque
    Var(x) => Variable(x)
    Call(f, args) => Apply(f, args)
    Fun(x, body) => Bind(x, body)
  }
}

impl @syntax.BindingSyntax for Expr with fn variable(x) {
  Var(x)
}

impl @syntax.BindingSyntax for Expr with fn apply(f, args) {
  Call(f, args)
}

impl @syntax.BindingSyntax for Expr with fn bind(x, body) {
  Fun(x, body)
}

test "quick start: free variables of an Expr" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let e = Fun(x, Call(Sym("+"), [Var(x), Var(y)]))
  let fv = @syntax.generic_free_variables(e)
  assert_true(fv.contains(y))
  assert_false(fv.contains(x))
}
```

Numbers and operator symbols project as `Opaque` because they contain no
variables. The type is `priv` because this example lives in a single package;
a library that exports its AST makes it `pub(all)` and states the methods it
promotes with `pub extend`. The operator of a call is its head, so rebuilding a call keeps the
operator.

## Everyday tasks

### Substitute without capture

`GenericSubstitution::apply_once` replaces free variables and renames `Fun`
binders when necessary:

```moonbit
test "capture-avoiding substitution on Expr" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let e = Fun(y, Call(Sym("+"), [Var(x), Var(y)]))
  let s = @substitution.GenericSubstitution::singleton(x, Var(y))
  let y1 = @core.Name::new("y_1")
  assert_eq(s.apply_once(e), Fun(y1, Call(Sym("+"), [Var(y), Var(y1)])))
}
```

### Evaluate partially

Substitute known values and keep the rest symbolic:

```moonbit
test "partial evaluation on Expr" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let e = Call(Sym("*"), [Var(x), Var(y)])
  let known = @substitution.GenericSubstitution::singleton(x, Num(3))
  assert_eq(known.apply_once(e), Call(Sym("*"), [Num(3), Var(y)]))
}
```

### Simplify with rewrite rules

Write rules against your own type and let the generic traversal find where
they apply:

```moonbit
fn fold_add(e : Expr) -> Expr? {
  match e {
    Call(Sym("+"), [Num(a), Num(b)]) => Some(Num(a + b))
    _ => None
  }
}

test "constant folding on Expr" {
  let x = @core.Name::new("x")
  let e = Call(Sym("*"), [Var(x), Call(Sym("+"), [Num(1), Call(Sym("+"), [Num(2), Num(3)])])])
  let rule = @rewrite.RuleName::unsafe_new("fold_add")
  assert_eq(
    @rewrite.generic_normalize(e, rule, fold_add, 10),
    NormalForm(term=Call(Sym("*"), [Var(x), Num(6)]), steps=2),
  )
  match @rewrite.generic_top_down_once(e, rule, fold_add) {
    Reduced(path~, ..) =>
      assert_eq(path.to_array(), [@rewrite.ApplyArgument(1), @rewrite.ApplyArgument(1)])
    NoStep => fail("expected a step")
  }
}
```

The path says: second argument of `*`, then second argument of the outer `+`.

### Rename a binder

`generic_alpha_rename_bound` renames the variable of a binder body and refuses
a name already in use:

```moonbit
test "rename a Fun parameter" {
  let x = @core.Name::new("x")
  let y = @core.Name::new("y")
  let z = @core.Name::new("z")
  let body = Call(Sym("+"), [Var(x), Var(y)])
  assert_true(@syntax.generic_alpha_rename_bound(body, x, y) is None)
  assert_eq(
    @syntax.generic_alpha_rename_bound(body, x, z),
    Some(Call(Sym("+"), [Var(z), Var(y)])),
  )
}
```

## Going further

### Test the adapter laws

The generic algorithms are correct only if `project` and the constructors
agree (the view laws of the [adapter design](../design/adapter.md)). Test them
on representative nodes:

```moonbit
fn rebuild(e : Expr) -> Expr {
  match @syntax.BindingSyntax::project(e) {
    Opaque => e
    Variable(x) => @syntax.BindingSyntax::variable(x)
    Apply(f, args) => @syntax.BindingSyntax::apply(f, args)
    Bind(x, body) => @syntax.BindingSyntax::bind(x, body)
  }
}

test "view laws" {
  let x = @core.Name::new("x")
  let samples = [
    Num(1),
    Sym("+"),
    Var(x),
    Call(Sym("+"), [Var(x), Num(2)]),
    Fun(x, Var(x)),
  ]
  for e in samples {
    assert_eq(rebuild(e), e)
    if @syntax.BindingSyntax::project(e) is Opaque {
      assert_eq(@syntax.generic_free_variables(e).length(), 0)
    }
  }
}
```

### Several operators under one view case

All calls project as `Apply`, and the operator travels in the head, so
`apply(head, args)` can rebuild any call. If your AST has separate node kinds
such as `Add(a, b)` and `Mul(a, b)`, give them a head that identifies the kind
(as `Sym` does here); otherwise `apply` cannot know which node to rebuild.

### Bridge your variable type

If your AST has its own variable type, map it injectively to `@core.Name`
(different variables, different names) in `project` and back in `variable`.

## Common pitfalls

- **Variables inside opaque nodes.** A node that projects as `Opaque` is never
  searched. If it contains variables, substitution misses them.
- **Calling trait methods with dot syntax.** Write
  `@syntax.BindingSyntax::project(e)`; the method forms are not promoted.
- **Losing the node kind in `apply`.** If two node kinds project to `Apply`
  and the head does not say which, rebuilding changes the AST.
- **Expecting repeated substitution.** `apply_once` substitutes once;
  iterate yourself if replacements mention the domain.

## Next steps

- [adapter design](../design/adapter.md) for the view laws and why they
  suffice.
- [syntax API](../api/syntax.md) for `BindingSyntax` and the generic
  analyses.
- [substitution tutorial](substitution.md) and [rewrite tutorial](rewrite.md)
  for the algorithms used here.
