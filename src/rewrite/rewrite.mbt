///|
/// Stable identifier for a reduction rule.
pub struct RuleName {
  value : String
} derive(Eq, Compare, Hash, Debug)

///|
/// Failures produced while validating a reduction rule name.
pub(all) enum RuleNameError {
  Empty
} derive(Eq, Debug)

///|
pub fn RuleName::new(value : String) -> Result[RuleName, RuleNameError] {
  if value.length() == 0 {
    Err(Empty)
  } else {
    Ok({ value, })
  }
}

///|
pub fn RuleName::unsafe_new(value : String) -> RuleName {
  match RuleName::new(value) {
    Ok(name) => name
    Err(Empty) => abort("reduction rule name must not be empty")
  }
}

///|
pub fn RuleName::value(self : RuleName) -> String {
  self.value
}

///|
/// One edge in a path from the root to a redex.
pub(all) enum ReductionFrame {
  BinderBody
  ApplyHead
  ApplyArgument(Int)
} derive(Eq, Debug)

///|
/// Root-to-redex path. The empty path identifies the root.
///
/// The type is abstract: its frames are not accessible outside the package.
/// Use `length` and `to_array` to read it.
///
/// A path is built from the redex up, one `prepend` per level, so the frames
/// are stored in that order, the reverse of the path. Paths built from one
/// another share their array: `prepend` pushes onto it when `self` is the
/// longest path stored there, and copies the prefix otherwise. A path only
/// reads the first `length` entries, and entries are never changed once
/// pushed, so a path cannot observe a longer one built from it. Building a
/// path of `n` frames by prepending therefore takes amortized `O(n)` time
/// instead of `O(n^2)` (issue #13).
struct ReductionPath {
  /// The frames from the redex up to the root; only the first `length`
  /// entries belong to this path.
  reversed : Array[ReductionFrame]
  /// The number of frames of this path.
  length : Int
}

///|
pub impl Eq for ReductionPath with fn equal(self, other) {
  if self.length != other.length {
    return false
  }
  for i in 0..<self.length {
    if self.reversed[i] != other.reversed[i] {
      return false
    }
  }
  true
}

///|
/// Shows the frames from the root to the redex, as `{ frames: [...] }`.
pub impl Debug for ReductionPath with fn to_repr(self) {
  @debug.Repr::record({ "frames": @debug.Repr(self.to_array()) })
}

///|
pub fn ReductionPath::root() -> ReductionPath {
  { reversed: [], length: 0, }
}

///|
/// Returns the path that takes `frame` from the root and then follows `self`.
/// Takes amortized constant time when `self` is the longest path built so far
/// from the same root path, as it is when a path is built from the redex up.
pub fn ReductionPath::prepend(
  self : ReductionPath,
  frame : ReductionFrame,
) -> ReductionPath {
  let reversed = if self.reversed.length() == self.length {
    self.reversed
  } else {
    self.reversed[0:self.length].to_owned()
  }
  reversed.push(frame)
  { reversed, length: self.length + 1, }
}

///|
/// Returns the number of frames. The root path has length zero.
pub fn ReductionPath::length(self : ReductionPath) -> Int {
  self.length
}

///|
/// Returns the frames from the root to the redex as a fresh array. Changing
/// the returned array does not change `self`.
pub fn ReductionPath::to_array(self : ReductionPath) -> Array[ReductionFrame] {
  Array::makei(self.length, fn(i) { self.reversed[self.length - 1 - i] })
}

///|
/// The result of exactly one reduction attempt.
pub(all) enum StepResult[T] {
  NoStep
  Reduced(
    before~ : @syntax.Term[T],
    after~ : @syntax.Term[T],
    rule~ : RuleName,
    path~ : ReductionPath
  )
} derive(Eq, Debug)

///|
/// The result of bounded repeated reduction.
pub(all) enum NormalizationResult[T] {
  NormalForm(term~ : @syntax.Term[T], steps~ : Int)
  StepLimitReached(term~ : @syntax.Term[T], steps~ : Int)
} derive(Eq, Debug)

///|
/// A complete bounded operational trace.
///
/// The type is abstract: its fields are not accessible outside the package.
/// Use `initial`, `steps`, and `result` to read it.
struct ReductionTrace[T] {
  initial : @syntax.Term[T]
  steps : Array[StepResult[T]]
  result : NormalizationResult[T]
} derive(Eq, Debug)

///|
pub fn[T] ReductionTrace::initial(self : ReductionTrace[T]) -> @syntax.Term[T] {
  self.initial
}

///|
/// Returns the successful steps in order as a fresh array. Changing the
/// returned array does not change `self`.
pub fn[T] ReductionTrace::steps(
  self : ReductionTrace[T],
) -> Array[StepResult[T]] {
  self.steps.copy()
}

///|
pub fn[T] ReductionTrace::result(
  self : ReductionTrace[T],
) -> NormalizationResult[T] {
  self.result
}

///|
/// Rewrites the first matching node in pre-order.
pub fn[T] top_down_once(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  match search_top_down(term, rule) {
    None => NoStep
    Some(found) => {
      let (after, path) = found.rebuild()
      Reduced(before=term, after~, rule=rule_name, path~)
    }
  }
}

///|
/// Rewrites the first matching node in post-order.
pub fn[T] bottom_up_once(
  term : @syntax.Term[T],
  rule_name : RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> StepResult[T] {
  match search_bottom_up(term, rule) {
    None => NoStep
    Some(found) => {
      let (after, path) = found.rebuild()
      Reduced(before=term, after~, rule=rule_name, path~)
    }
  }
}

///|
/// Repeats a single-step reducer until no step exists or the limit is reached.
pub fn[T] normalize(
  term : @syntax.Term[T],
  step : (@syntax.Term[T]) -> StepResult[T],
  max_steps : Int,
) -> NormalizationResult[T] {
  let mut current = term
  let mut count = 0
  while count < max_steps {
    match step(current) {
      NoStep =>
        return NormalizationResult::NormalForm(term=current, steps=count)
      Reduced(after~, ..) => {
        current = after
        count = count + 1
      }
    }
  }
  match step(current) {
    NoStep => NormalizationResult::NormalForm(term=current, steps=count)
    Reduced(_) =>
      NormalizationResult::StepLimitReached(term=current, steps=count)
  }
}

///|
/// Records every successful step produced by the supplied reducer.
pub fn[T] trace(
  term : @syntax.Term[T],
  step : (@syntax.Term[T]) -> StepResult[T],
  max_steps : Int,
) -> ReductionTrace[T] {
  let initial = term
  let steps : Array[StepResult[T]] = []
  let mut current = term
  let mut count = 0
  while count < max_steps {
    match step(current) {
      NoStep =>
        return {
          initial,
          steps,
          result: NormalizationResult::NormalForm(term=current, steps=count),
        }
      Reduced(after~, ..) as reduced => {
        steps.push(reduced)
        current = after
        count = count + 1
      }
    }
  }
  let result = match step(current) {
    NoStep => NormalizationResult::NormalForm(term=current, steps=count)
    Reduced(_) =>
      NormalizationResult::StepLimitReached(term=current, steps=count)
  }
  { initial, steps, result, }
}
