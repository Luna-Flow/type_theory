///|
pub struct TypeContext {
  entries : Array[(@core.Name, Ty)]
} derive(Eq, Debug)

///|
pub fn TypeContext::empty() -> TypeContext {
  { entries: [] }
}

///|
pub fn TypeContext::extend(
  self : TypeContext,
  name : @core.Name,
  ty : Ty,
) -> TypeContext {
  let entries = self.entries.copy()
  entries.push((name, ty))
  { entries, }
}

///|
pub fn TypeContext::lookup(self : TypeContext, name : @core.Name) -> Ty? {
  for i = self.entries.length() - 1; i >= 0; i = i - 1 {
    if self.entries[i].0 == name {
      return Some(self.entries[i].1)
    }
  }
  None
}

///|
pub fn TypeContext::to_array(self : TypeContext) -> Array[(@core.Name, Ty)] {
  self.entries.copy()
}
