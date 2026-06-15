# Contribution Guidelines

## Workflow

1. Keep changes within the owning package and preserve the dependency direction.
2. Add regression tests for every binding, scope, or reduction bug.
3. Run `./ready_to_pr.sh` before review.
4. Review generated `pkg.generated.mbti` changes as public API changes.

## Style

- Use `moon fmt` and current MoonBit syntax.
- Prefer pure transformations and explicit structured outcomes.
- Public validation and scope failures must return structured data rather than
  abort. Reserve `abort` and `unsafe_*` APIs for documented internal invariants.
- Use `pub(open)` only for extension contracts intended for downstream types.
- Conventional commits must be concise English summaries without file paths.

## Semantic Changes

Changes to substitution, alpha-equivalence, De Bruijn shifting, beta
instantiation, quote, or fuel accounting require updates to the correctness
checklist and cross-representation tests.
