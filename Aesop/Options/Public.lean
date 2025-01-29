import Lean

open Lean Lean.Meta

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
  When Aesop fails to prove a goal, it reports the goals that remain after safe
  rules have been applied exhaustively to the root goal, the safe
  descendants of the root goal, and so on (i.e., after the "safe prefix" of the
  search tree has been unfolded). However, it is possible for the search to fail
  before the safe prefix has been completely generated. In this case, Aesop
  expands the safe prefix after the fact. This option limits the number of
  additional rule applications generated during this process. 0 means no limit.
  -/
  maxSafePrefixRuleApplications := 50
  /--
  Heartbeat limit for individual Aesop rules. If a rule goes over this limit, it
  fails, but Aesop itself continues until it reaches the limit set by the
  `maxHeartbeats` option. If `maxRuleHeartbeats = 0` or `maxRuleHeartbeats` is
  greater than `maxHeartbeats`, the `maxHeartbeats` limit is used for the
  individual rules as well.
  -/
  maxRuleHeartbeats := 0
  /--
  Heartbeat limit for Aesop's builtin `simp` rule. If `simp` goes over this
  limit, Aesop fails. If `maxSimpHeartbeats = 0`, there is no limit for `simp`
  (but the global heartbeat limit still applies).
  -/
  maxSimpHeartbeats := 0
  /--
  Heartbeat limit for Aesop's builtin `unfold` rule. If `unfold` goes over this
  limit, Aesop fails. If `maxUnfoldHeartbeats = 0`, there is no limit for
  `unfold` (but the global heartbeat limit still applies).
  -/
  maxUnfoldHeartbeats := 0
  /--
  The transparency used by the `applyHyps` builtin rule. The rule applies a
  hypothesis `h : T` if `T ≡ ∀ (x₁ : X₁) ... (xₙ : Xₙ), Y` at the given
  transparency and if additionally the goal's target is defeq to `Y` at the
  given transparency.
  -/
  applyHypsTransparency : TransparencyMode := .default
  /--
  The transparency used by the `assumption` builtin rule. The rule applies a
  hypothesis `h : T` if `T` is defeq to the goal's target at the given
  transparency.
  -/
  assumptionTransparency : TransparencyMode := .default
  /--
  The transparency used by the `destructProducts` builtin rule. The rule splits
  a hypothesis `h : T` if `T` is defeq to a product-like type (e.g. `T ≡ A ∧ B`
  or `T ≡ A × B`) at the given transparency.

  Note: we can index this rule only if the transparency is `.reducible`. With
  any other transparency, the rule becomes unindexed and is applied to every
  goal.
  -/
  destructProductsTransparency : TransparencyMode := .reducible
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
  /--
  Enable the builtin `simp` normalisation rule.
  -/
  enableSimp := true
  /--
  Use `simp_all`, rather than `simp at *`, for the builtin `simp` normalisation
  rule.
  -/
  useSimpAll := true
  /--
  Use simp theorems from the default `simp` set, i.e. those tagged with
  `@[simp]`. If this option is `false`, Aesop uses only Aesop-specific simp
  theorems, i.e. those tagged with `@[aesop simp]`. Note that the congruence
  lemmas from the default `simp` set are always used.
  -/
  useDefaultSimpSet := true
  /--
  Enable the builtin `unfold` normalisation rule.
  -/
  enableUnfold := true
  deriving Inhabited, BEq, Repr

/--
(aesop) Only for use by Aesop developers. Enables dynamic script structuring.
-/
register_option aesop.dev.dynamicStructuring : Bool := {
  descr := "(aesop) Only for use by Aesop developers. Enables dynamic script structuring."
  defValue := true
}

/--
(aesop) Only for use by Aesop developers. Uses static structuring instead of
dynamic structuring if no metavariables appear in the proof.
-/
register_option aesop.dev.optimizedDynamicStructuring : Bool := {
  descr := "(aesop) Only for use by Aesop developers. Uses static structuring instead of dynamic structuring if no metavariables appear in the proof."
  defValue := true
}

/--
(aesop) Only for use by Aesop developers. Generates a script even if none was requested.
-/
register_option aesop.dev.generateScript : Bool := {
  descr := "(aesop) Only for use by Aesop developers. Generates a script even if none was requested."
  defValue := false
}

/--
(aesop) Only for use by Aesop developers. Enables the new stateful forward reasoning engine.
-/
register_option aesop.dev.statefulForward : Bool := {
  descr := "(aesop) Only for use by Aesop developers. Enables the new stateful forward reasoning engine."
  defValue := true
}

/--
(aesop) Warn when apply builder is applied to a rule with conclusion of the form A ↔ B
-/
register_option aesop.warn.applyIff : Bool := {
  descr := "(aesop) Warn when apply builder is applied to a rule with conclusion of the form A ↔ B"
  defValue := true
}

end Aesop
