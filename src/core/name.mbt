///|
/// A variable name. Equality identifies variables in named syntax.
pub struct Name {
  text : String
} derive(Eq, Compare, Hash, Debug)

///|
pub fn Name::new(text : String) -> Name {
  { text, }
}

///|
pub fn Name::text(self : Name) -> String {
  self.text
}

///|
/// Chooses a name not present in `used`, preserving `hint` when possible.
pub fn fresh_name(hint : Name, used : @hashset.HashSet[Name]) -> Name {
  if !used.contains(hint) {
    return hint
  }
  let mut suffix = 1
  while true {
    let candidate = Name::new(hint.text + "_" + suffix.to_string())
    if !used.contains(candidate) {
      return candidate
    }
    suffix = suffix + 1
  }
  abort("unreachable")
}
