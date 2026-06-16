///|
pub struct Signature {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, Debug)

///|
pub fn Signature::empty() -> Signature {
  { entries: [] }
}

///|
pub fn Signature::extend(
  self : Signature,
  name : @core.Name,
  ty : Ty,
) -> Signature {
  let entries = self.entries.copy()
  entries.push((name, ty))
  { entries, }
}

///|
pub fn Signature::lookup(self : Signature, name : @core.Name) -> Ty? {
  for i = self.entries.length() - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
pub fn Signature::to_array(self : Signature) -> Array[(@core.Name, Ty)] {
  self.entries.copy()
}
