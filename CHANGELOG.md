# Changelog

All notable changes to `Luna-Flow/type_theory` are recorded here.

## Unreleased

### Changed

- Migrated to MoonBit 0.10 (`moonc` 0.10 or newer is required).
- `moon.mod` declares the source directory with `source = "src"` instead of
  `options(source: ...)`.
- Trait methods that were implicitly promoted to methods are now promoted
  explicitly in each package's `extends.mbt`: `equal` on every type deriving
  `Eq`, and `compare` and `hash` on `Name` and `RuleName`. These now appear in
  the generated interfaces.
- Test fixtures and blackbox tests follow the 0.10 rules: the adapter test AST
  is `priv`, and blackbox tests qualify package names.
- `@hashset.from_array` calls were replaced by the `@hashset.HashSet([..])`
  constructor.

### Deprecated

- `Context::extend`, `Telescope::extend` (in `core`) and `Signature::extend`,
  `TypeContext::extend` (in `stlc`): `extend` is now a reserved word. Use
  `extend_with`; the old names remain as deprecated aliases.
- The implicit method forms `not_equal`, `op_lt`, `op_le`, `op_gt`, `op_ge`,
  `hash_combine` and `to_repr` are hidden and deprecated; use the operators,
  the traits and `Repr(x)`.
- The method forms of `BindingSyntax` on `Term` (`term.project()`,
  `Term::variable`, `Term::apply`, `Term::bind`) are hidden and deprecated; use
  `@syntax.BindingSyntax::project(term)` and the `Term` constructors.

### Documentation

- Documentation rewritten: API reference, tutorial and design note for every
  package, a semantic architecture guide, and a Typst note with the De Bruijn
  index lemmas, with zh_CN and ja_JP translations.
- `CORRECTNESS_CHECKLIST.md` records the spine shape of NbE normal forms, the
  missing unit eta law, and a known issue in STLC redex inference.
