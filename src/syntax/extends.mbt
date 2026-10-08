///|
pub extend Term with Eq::{equal}

///|
#deprecated("Use `!=` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with Eq::{not_equal}

///|
#deprecated("Use `Repr(x)` or `@debug.to_string(x)` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with Debug::{to_repr}

///|
#deprecated("Use `BindingSyntax::project(term)` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with BindingSyntax::{project}

///|
#deprecated("Use `Term::Variable(name)` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with BindingSyntax::{variable}

///|
#deprecated("Use `Term::Apply(head, arguments)` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with BindingSyntax::{apply}

///|
#deprecated("Use `Term::Bind(name, body)` instead", skip_current_package=true)
#doc(hidden)
pub extend Term with BindingSyntax::{bind}
