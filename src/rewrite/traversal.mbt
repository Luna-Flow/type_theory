// Bounded-stack traversal (issue #13).
//
// The traversals are specified recursively: `top_down_once` tries the rule at
// a node and otherwise recurses into the body, the head and the arguments in
// order; `bottom_up_once` recurses first and tries the rule at the node only
// when no child has a redex. A step found at depth `d` then rebuilds the `d`
// nodes above it and prepends one frame per level on the way back up.
// Implemented as host recursion, a term nested `d` levels deep needs `d` host
// frames, and the js and wasm stacks overflow at a depth of a few thousand.
//
// The search runs instead as one loop that keeps the ancestors of the current
// position in a heap array, root first:
//
// - `Ancestor` is one entry of that array: a parent node, already projected,
//   and the edge taken from it. Read in order, the edges are the path from
//   the root to the current position.
// - The loop either enters a node (try the rule, or descend into its first
//   child), leaves a subtree in which no redex was found (pop ancestors until
//   one has a next child), or, in post-order, tries the rule at a node whose
//   children have all been searched.
//
// Rule calls happen in the order of the recursive definition, so the chosen
// redex is the same. Once it is found, the array is exactly the path to it,
// and `Found::rebuild` replaces the redex and rebuilds the ancestors from the
// innermost outwards, as the recursion did while returning.

///|
/// One ancestor of the position being searched: a parent node with its
/// projected fields, and the child of it on the way to the position.
priv enum Ancestor[N] {
  /// The body of the binder `parent = Bind(name, body)`.
  BodyOf(N, @core.Name)
  /// The head of the application `parent = Apply(head, arguments)`.
  HeadOf(N, N, Array[N])
  /// Argument `index` of the application `parent = Apply(head, arguments)`.
  ArgumentOf(N, N, Array[N], Int)
}

///|
/// The parent node of an ancestor entry.
fn[N] Ancestor::parent(self : Ancestor[N]) -> N {
  match self {
    BodyOf(parent, _) | HeadOf(parent, _, _) | ArgumentOf(parent, _, _, _) =>
      parent
  }
}

///|
/// The edge from the parent to the child on the path.
fn[N] Ancestor::frame(self : Ancestor[N]) -> ReductionFrame {
  match self {
    BodyOf(_, _) => BinderBody
    HeadOf(_, _, _) => ApplyHead
    ArgumentOf(_, _, _, index) => ApplyArgument(index)
  }
}

///|
/// The next child of the parent after the one on the path, as the ancestor
/// entry that leads to it and the child itself. `None` when the child on the
/// path is the last one: the body of a binder or the last argument.
fn[N] Ancestor::next_child(self : Ancestor[N]) -> (Ancestor[N], N)? {
  match self {
    BodyOf(_, _) => None
    HeadOf(parent, head, arguments) =>
      if arguments.length() > 0 {
        Some((ArgumentOf(parent, head, arguments, 0), arguments[0]))
      } else {
        None
      }
    ArgumentOf(parent, head, arguments, index) =>
      if index + 1 < arguments.length() {
        Some(
          (ArgumentOf(parent, head, arguments, index + 1), arguments[index + 1]),
        )
      } else {
        None
      }
  }
}

///|
/// The ancestor entry for descending into the first child of `node`, and that
/// child. `None` for a node without children: an opaque leaf or a variable.
fn[N : @syntax.BindingSyntax] first_child(node : N) -> (Ancestor[N], N)? {
  match @syntax.BindingSyntax::project(node) {
    @syntax.BindingView::Opaque | @syntax.BindingView::Variable(_) => None
    @syntax.BindingView::Bind(name, body) => Some((BodyOf(node, name), body))
    @syntax.BindingView::Apply(head, arguments) =>
      Some((HeadOf(node, head, arguments), head))
  }
}

///|
/// A redex found by a search: the ancestors of its position, root first, and
/// the result of the rule on it.
priv struct Found[N] {
  ancestors : Array[Ancestor[N]]
  after : N
}

///|
/// Rebuilds the searched term with the redex replaced by `after`, and returns
/// it with the path to the redex.
///
/// The ancestors are rebuilt from the innermost outwards, with the same trait
/// constructors and the same argument arrays as the recursive traversal, so
/// unchanged subterms are shared with the original term.
fn[N : @syntax.BindingSyntax] Found::rebuild(
  self : Found[N],
) -> (N, ReductionPath) {
  let mut node = self.after
  let mut path = ReductionPath::root()
  for i = self.ancestors.length() - 1; i >= 0; i = i - 1 {
    let ancestor = self.ancestors[i]
    node = match ancestor {
      BodyOf(_, name) => @syntax.BindingSyntax::bind(name, node)
      HeadOf(_, _, arguments) => @syntax.BindingSyntax::apply(node, arguments)
      ArgumentOf(_, head, arguments, index) => {
        let next_arguments = arguments.copy()
        next_arguments[index] = node
        @syntax.BindingSyntax::apply(head, next_arguments)
      }
    }
    path = path.prepend(ancestor.frame())
  }
  (node, path)
}

///|
/// The next step of a search.
priv enum Walk[N] {
  /// Search the subtree rooted at this node; its ancestors are on the stack.
  Enter(N)
  /// The subtree just searched contains no redex.
  Leave
  /// Post-order only: every child of this node has been searched without
  /// success; try the rule at the node itself.
  Exit(N)
}

///|
/// Finds the first redex of `rule` in pre-order: the rule is tried at a node
/// before its children: the body of a binder, or the head and then the
/// arguments of an application in order. The host stack depth is constant.
fn[N : @syntax.BindingSyntax] search_top_down(
  node : N,
  rule : (N) -> N?,
) -> Found[N]? {
  let ancestors : Array[Ancestor[N]] = []
  for walk = Enter(node) {
    match walk {
      Enter(current) =>
        match rule(current) {
          Some(after) => break Some({ ancestors, after, })
          None =>
            match first_child(current) {
              Some((ancestor, child)) => {
                ancestors.push(ancestor)
                continue Enter(child)
              }
              None => continue Leave
            }
        }
      Leave =>
        match ancestors.pop() {
          None => break None
          Some(ancestor) =>
            match ancestor.next_child() {
              Some((next, child)) => {
                ancestors.push(next)
                continue Enter(child)
              }
              None => continue Leave
            }
        }
      Exit(_) => abort("pre-order search never tries a node after its children")
    }
  }
}

///|
/// Finds the first redex of `rule` in post-order: the rule is tried at a node
/// after all of its children, which are searched in the same order as in
/// `search_top_down`. The host stack depth is constant.
fn[N : @syntax.BindingSyntax] search_bottom_up(
  node : N,
  rule : (N) -> N?,
) -> Found[N]? {
  let ancestors : Array[Ancestor[N]] = []
  for walk = Enter(node) {
    match walk {
      Enter(current) =>
        match first_child(current) {
          Some((ancestor, child)) => {
            ancestors.push(ancestor)
            continue Enter(child)
          }
          None => continue Exit(current)
        }
      Exit(current) =>
        match rule(current) {
          Some(after) => break Some({ ancestors, after, })
          None => continue Leave
        }
      Leave =>
        match ancestors.pop() {
          None => break None
          Some(ancestor) =>
            match ancestor.next_child() {
              Some((next, child)) => {
                ancestors.push(next)
                continue Enter(child)
              }
              None => continue Exit(ancestor.parent())
            }
        }
    }
  }
}
