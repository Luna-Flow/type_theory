///|
pub extend Context with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend Context with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend Context with Debug::{to_repr}

///|
pub extend Name with Eq::{equal}

///|
pub extend Name with Compare::{compare}

///|
pub extend Name with Hash::{hash}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Eq::{not_equal}

///|
#deprecated("Use `<` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Compare::{op_lt}

///|
#deprecated("Use `<=` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Compare::{op_le}

///|
#deprecated("Use `>` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Compare::{op_gt}

///|
#deprecated("Use `>=` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Compare::{op_ge}

///|
#deprecated("Use `Hash::hash_combine` via the trait instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Hash::{hash_combine}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend Name with Debug::{to_repr}

///|
pub extend Renaming with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend Renaming with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend Renaming with Debug::{to_repr}
