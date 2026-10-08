///|
pub extend NbeResult with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend NbeResult with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend NbeResult with Debug::{to_repr}
