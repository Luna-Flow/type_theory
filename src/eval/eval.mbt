///|
/// Standard operational traversal choices.
pub(all) enum Strategy {
  NormalOrder
  ApplicativeOrder
  WeakHead
  FullNormal
} derive(Eq, Debug)

// Bounded-stack traversals (issue #13).
//
// The searches of this file are specified recursively, like the traversals of
// `@rewrite`: a step found at depth `d` rebuilds the `d` nodes above it while
// the recursion returns. They run instead as loops that keep the ancestors of
// the current position in a heap array, root first, so the host stack depth
// is constant whatever the nesting depth of the term. The rule is tried at the
// same positions in the same order as by the recursive definition, so the
// chosen redex, the rebuilt term and the path are unchanged.

///|
/// One ancestor of the position being searched: a parent node with its
/// fields, and the child of it on the way to the position.
priv enum Ancestor[T] {
  /// The body of the binder `parent = Bind(name, body)`.
  BodyOf(@syntax.Term[T], @core.Name)
  /// The head of the application `parent = Apply(head, arguments)`.
  HeadOf(@syntax.Term[T], @syntax.Term[T], Array[@syntax.Term[T]])
  /// Argument `index` of the application `parent = Apply(head, arguments)`.
  /// `root_failed` records that the rule has already been tried at `parent`
  /// and did not apply (see `applicative_once`).
  ArgumentOf(
    @syntax.Term[T],
    @syntax.Term[T],
    Array[@syntax.Term[T]],
    Int,
    Bool
  )
}

///|
/// Builds the step that rewrites, in `before`, the position reached through
/// `ancestors` (root first) to `after`.
///
/// The ancestors are rebuilt from the innermost outwards and the path is
/// prepended one frame per level, as the recursive search did while returning.
fn[T] rebuild_step(
  before : @syntax.Term[T],
  ancestors : Array[Ancestor[T]],
  after : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
) -> @rewrite.StepResult[T] {
  let mut node = after
  let mut path = @rewrite.ReductionPath::root()
  for i = ancestors.length() - 1; i >= 0; i = i - 1 {
    match ancestors[i] {
      BodyOf(_, name) => {
        node = Bind(name, node)
        path = path.prepend(BinderBody)
      }
      HeadOf(_, _, arguments) => {
        node = Apply(node, arguments)
        path = path.prepend(ApplyHead)
      }
      ArgumentOf(_, head, arguments, index, _) => {
        let next_arguments = arguments.copy()
        next_arguments[index] = node
        node = Apply(head, next_arguments)
        path = path.prepend(ApplyArgument(index))
      }
    }
  }
  Reduced(before~, after=node, rule=rule_name, path~)
}

///|
/// Weak-head search: the rule is tried at the root, then along the chain of
/// application heads, and nowhere else.
fn[T] weak_head_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> @rewrite.StepResult[T] {
  let ancestors : Array[Ancestor[T]] = []
  for current = term {
    match rule(current) {
      Some(after) => break rebuild_step(term, ancestors, after, rule_name)
      None =>
        match current {
          Apply(head, arguments) => {
            ancestors.push(HeadOf(current, head, arguments))
            continue head
          }
          _ => break NoStep
        }
    }
  }
}

///|
/// The next step of the applicative-order search.
priv enum Walk[T] {
  /// Search the subtree rooted at this term; its ancestors are on the stack.
  Enter(@syntax.Term[T])
  /// The subtree just searched contains no step.
  Leave
  /// Every position strictly below this term has been searched without
  /// success; try the rule at the term itself.
  Exit(@syntax.Term[T])
}

///|
/// Leftmost-innermost search on the curried reading of application spines.
///
/// `Apply(h, [a0, ..., an])` is read as `(...((h a0) a1) ...) an`. Post-order
/// on that reading visits `h`, `a0`, the prefix `h a0`, `a1`, the prefix
/// `h a0 a1`, and so on. Only the whole application is a position of the
/// n-ary tree, so a prefix is never rewritten on its own: after argument `i`,
/// if the rule applies to the prefix `Apply(h, [a0, ..., ai])`, the rule is
/// tried on the whole application at this point instead of after the last
/// argument. The reported step is therefore always the rule applied at a real
/// position, and every position is still tried.
///
/// If that early attempt fails, the whole application is not tried again: the
/// `ArgumentOf` entry carries this as `root_failed`, and the search leaves the
/// application without a step after its last argument.
fn[T] applicative_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
) -> @rewrite.StepResult[T] {
  let ancestors : Array[Ancestor[T]] = []
  for walk = Enter(term) {
    match walk {
      Enter(current) =>
        match current {
          Value(_) | Variable(_) => continue Exit(current)
          Bind(name, body) => {
            ancestors.push(BodyOf(current, name))
            continue Enter(body)
          }
          Apply(head, arguments) => {
            ancestors.push(HeadOf(current, head, arguments))
            continue Enter(head)
          }
        }
      Exit(current) =>
        match rule(current) {
          Some(after) => break rebuild_step(term, ancestors, after, rule_name)
          None => continue Leave
        }
      Leave =>
        match ancestors.pop() {
          None => break NoStep
          Some(BodyOf(parent, _)) => continue Exit(parent)
          Some(HeadOf(parent, head, arguments)) =>
            if arguments.length() > 0 {
              ancestors.push(ArgumentOf(parent, head, arguments, 0, false))
              continue Enter(arguments[0])
            } else {
              continue Exit(parent)
            }
          Some(ArgumentOf(parent, head, arguments, index, root_failed)) => {
            // argument `index` has no step: try the whole application early
            // if the prefix ending at this argument is a redex
            let mut root_failed = root_failed
            if index < arguments.length() - 1 &&
              !root_failed &&
              rule(Apply(head, arguments[0:index + 1].to_owned())) is Some(_) {
              match rule(parent) {
                Some(after) =>
                  break rebuild_step(term, ancestors, after, rule_name)
                None => root_failed = true
              }
            }
            if index + 1 < arguments.length() {
              ancestors.push(
                ArgumentOf(parent, head, arguments, index + 1, root_failed),
              )
              continue Enter(arguments[index + 1])
            } else if root_failed {
              continue Leave
            } else {
              continue Exit(parent)
            }
          }
        }
    }
  }
}

///|
/// Performs at most one reduction according to the selected strategy.
pub fn[T] reduce_once(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
) -> @rewrite.StepResult[T] {
  match strategy {
    NormalOrder | FullNormal => @rewrite.top_down_once(term, rule_name, rule)
    ApplicativeOrder => applicative_once(term, rule_name, rule)
    WeakHead => weak_head_once(term, rule_name, rule)
  }
}

///|
/// Normalizes solely by repeatedly invoking `reduce_once`.
pub fn[T] evaluate(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
  max_steps : Int,
) -> @rewrite.NormalizationResult[T] {
  @rewrite.normalize(
    term,
    fn(current) { reduce_once(current, rule_name, rule, strategy) },
    max_steps,
  )
}

///|
/// Produces an auditable operational reduction trace.
pub fn[T] trace(
  term : @syntax.Term[T],
  rule_name : @rewrite.RuleName,
  rule : (@syntax.Term[T]) -> @syntax.Term[T]?,
  strategy : Strategy,
  max_steps : Int,
) -> @rewrite.ReductionTrace[T] {
  @rewrite.trace(
    term,
    fn(current) { reduce_once(current, rule_name, rule, strategy) },
    max_steps,
  )
}
