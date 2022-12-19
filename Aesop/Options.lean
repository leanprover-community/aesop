import Lean.Meta.TransparencyMode

open Lean.Meta (TransparencyMode)

namespace Aesop

inductive Strategy
  | bestFirst
  | depthFirst
  | breadthFirst
  deriving Inhabited, BEq, Repr

/--
Options that modify Aesop's behaviour. Available options are:

- `strategy`: the search strategy to use.
- `maxRuleApplicationDepth`: maximum number of rule applications in any branch
  of the search tree, aka maximum search depth. When a branch exceeds this
  limit, it is considered unprovable; other branches may still be explored. 0
  means no limit.
- `maxRuleApplications`: maximum number of rule applications in the search tree.
  When this limit is exceeded, the search ends. 0 means no limit.
- `maxGoals`: maximum number of goals in the search tree. When this limit is
  exceeded, the search ends. 0 means no limit.
- `maxNormIterations`: maximum number of norm rules applied to a *single* goal.
  When this limit is exceeded, normalisation is likely stuck in an infinite loop
  so Aesop fails. 0 means no limit.
- `introsTransparency?`: if `true`, the builtin `intros` rule unfolds the goal's
  target with the given transparency to discover `∀` binders. For example, with
  `def T := ∀ x y : Nat, x = y`, `introsTransparency? := some .default` and goal
  `⊢ T`, the `intros` rule produces the goal `x, y : Nat ⊢ x = y`. With
  `introsTransparency? := some .reducible`, it produces `⊢ T`. With
  `introsTransparency? := none`, it only introduces arguments which are
  syntactically bound by `∀` binders, so it also produces `⊢ T`.
- `terminal`: if `true`, Aesop succeeds only if it proves the goal. If `false`,
  Aesop always succeeds and reports the goals remaining after safe rules were
  applied.
- `warnOnNonterminal`: print a warning when Aesop does not prove the goal.
- `traceScript`: print a tactic script as a `Try this:` suggestion.
-/
structure Options where
  strategy := Strategy.bestFirst
  maxRuleApplicationDepth := 30
  maxRuleApplications := 200
  maxGoals := 0
  maxNormIterations := 100
  introsTransparency? : Option TransparencyMode := none
  terminal := false
  warnOnNonterminal := true
  traceScript := false
  deriving Inhabited, BEq, Repr

end Aesop
