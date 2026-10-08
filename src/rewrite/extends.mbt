///|
pub extend RuleName with Eq::{equal}

///|
pub extend RuleName with Compare::{compare}

///|
pub extend RuleName with Hash::{hash}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Eq::{not_equal}

///|
#deprecated("Use `<` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Compare::{op_lt}

///|
#deprecated("Use `<=` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Compare::{op_le}

///|
#deprecated("Use `>` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Compare::{op_gt}

///|
#deprecated("Use `>=` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Compare::{op_ge}

///|
#deprecated("Use `Hash::hash_combine` via the trait instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Hash::{hash_combine}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleName with Debug::{to_repr}

///|
pub extend RuleNameError with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleNameError with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend RuleNameError with Debug::{to_repr}

///|
pub extend ReductionFrame with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionFrame with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionFrame with Debug::{to_repr}

///|
pub extend ReductionPath with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionPath with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionPath with Debug::{to_repr}

///|
pub extend StepResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend StepResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend StepResult with Debug::{to_repr}

///|
pub extend NormalizationResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend NormalizationResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend NormalizationResult with Debug::{to_repr}

///|
pub extend ReductionTrace with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionTrace with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend ReductionTrace with Debug::{to_repr}

///|
pub extend GenericStepResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend GenericStepResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend GenericStepResult with Debug::{to_repr}

///|
pub extend GenericNormalizationResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend GenericNormalizationResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend GenericNormalizationResult with Debug::{to_repr}
