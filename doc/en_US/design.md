# Design

The operational semantics is defined by structured single-step reduction.
Bounded normalizers and traces repeatedly invoke that interface.

NbE is an independent denotational implementation using lazy delayed terms,
closures, neutral levels, and quote. It shares De Bruijn scope and binder
primitives with the operational reducer and is checked for result agreement.

Named and De Bruijn syntax are both public. Conversion into De Bruijn removes
alpha-renaming from the reduction kernel; conversion back selects deterministic
fresh names.

Expected failures at public boundaries are represented as structured data.
`RuleName::new`, for example, returns `RuleNameError::Empty` for an empty name.
Aborting `unsafe_*` constructors are reserved for callers that already establish
the corresponding internal invariant.
