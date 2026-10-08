///|
pub extend DbTerm with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend DbTerm with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend DbTerm with Debug::{to_repr}

///|
pub extend ScopeError with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend ScopeError with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend ScopeError with Debug::{to_repr}

///|
pub extend DbStepResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend DbStepResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend DbStepResult with Debug::{to_repr}

///|
pub extend DbNormalizationResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend DbNormalizationResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend DbNormalizationResult with Debug::{to_repr}
