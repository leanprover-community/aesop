import Lean.Meta.TransparencyMode

open Lean.Meta (TransparencyMode)

namespace Aesop

set_option linter.missingDocs true

/--
Search strategies which Aesop can use.
-/
inductive Strategy
  /--
  Best-first search. This is the default strategy.
  -/
  | bestFirst
  /--
  Depth-first search. Whenever a rule is applied, Aesop immediately tries to
  solve each of its subgoals (from left to right), up to the maximum rule
  application depth. Goal and rule priorities are ignored, except to decide
  which rule is applied first.
  -/
  | depthFirst
  /--
  Breadth-first search. Aesop always works on the oldest unsolved goal. Goal and
  rule priorities are ignored, except to decide which rule is applied first.
  -/
  | breadthFirst
  deriving Inhabited, BEq, Repr

/--
Options which modify the behaviour of the `aesop` tactic.
-/
structure Options where
  /--
  The search strategy used by Aesop.
  -/
  strategy := Strategy.bestFirst
  /--
  The maximum number of rule applications in any branch of the search tree
  (i.e., the maximum search depth). When a branch exceeds this limit, it is
  considered unprovable, but other branches may still be explored. 0 means no
  limit.
  -/
  maxRuleApplicationDepth := 30
  /--
  Maximum total number of rule applications in the search tree. When this limit
  is exceeded, the search ends. 0 means no limit.
  -/
  maxRuleApplications := 200
  /--
  Maximum total number of goals in the search tree. When this limit is exceeded,
  the search ends. 0 means no limit.
  -/
  maxGoals := 0
  /--
  Maximum number of norm rules applied to a single goal. When this limit is
  exceeded, normalisation is likely stuck in an infinite loop, so Aesop fails. 0
  means no limit.
  -/
  maxNormIterations := 100
  /--
  If this option is not `none`, the builtin `intros` rule unfolds the goal's
  target with the given transparency to discover `∀` binders. For example, with
  `def T := ∀ x y : Nat, x = y`, `introsTransparency? := some .default` and goal
  `⊢ T`, the `intros` rule produces the goal `x, y : Nat ⊢ x = y`. With
  `introsTransparency? := some .reducible`, it produces `⊢ T`. With
  `introsTransparency? := none`, it only introduces arguments which are
  syntactically bound by `∀` binders, so it also produces `⊢ T`.
  -/
  introsTransparency? : Option TransparencyMode := none
  /--
  If `true`, Aesop succeeds only if it proves the goal. If `false`, Aesop always
  succeeds and reports the goals remaining after safe rules were applied.
  -/
  terminal := false
  /--
  If `true`, print a warning when Aesop does not prove the goal.
  -/
  warnOnNonterminal := true
  /--
  If Aesop proves a goal and this option is `true`, Aesop prints a tactic proof
  as a `Try this:` suggestion.
  -/
  traceScript := false
  deriving Inhabited, BEq, Repr

/--
Options which modify the behaviour of the builtin `simp` normalisation rule.
Extends `Lean.Meta.Simp.ConfigCtx`, so any option declared there is also valid
here. For example, you can use `aesop (simp_config := { arith := true })` to get
behaviour similar to `simp (config := { arith := true })` (aka `simp_arith`).
-/
structure SimpConfig extends Lean.Meta.Simp.ConfigCtx where
  maxDischargeDepth := 1 -- We reduce the default max discharge depth from 2 to 1.
  /--
  If `true`, the `simp` normalisation rule works like `simp_all`. This means it
  uses hypotheses which are propositions or equations to simplify other
  hypotheses and the target.

  If `false`, the `simp` normalisation rule works like `simp at *`. This means
  hypotheses are simplified, but are not used to simplify other hypotheses and
  the target. -/
  useHyps := true

end Aesop
