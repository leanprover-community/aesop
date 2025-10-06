/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

namespace Aesop

open Lean Lean.Meta

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. -/
def ForwardState.applyGoalDiff (rs : LocalRuleSet) (diff : GoalDiff)
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) := do
  if ! aesop.dev.statefulForward.get (← getOptions) then
    -- We still update the hyp types since these are also used by stateless
    -- forward reasoning.
    return ({ fs with hypTypes := ← updateHypTypes fs.hypTypes } , #[])
  let fs ← diff.oldGoal.withContext do
    diff.removedFVars.foldM (init := fs) λ fs h => do eraseHyp h fs
  diff.newGoal.withContext do
    let (fs, ruleMatches) ←
      diff.addedFVars.foldM (init := (fs, ∅)) λ (fs, ruleMatches) h => do
        addHyp h fs ruleMatches
    if ← diff.targetChanged' then
      updateTarget fs ruleMatches
    else
      return (fs, ruleMatches)
where
  eraseHyp (h : FVarId) (fs : ForwardState) : BaseM ForwardState :=
    withConstAesopTraceNode .forward (return m!"erase hyp {Expr.fvar h} ({h.name})") do
      return fs.eraseHyp h (← rpinf (← h.getType))

  addHyp (h : FVarId) (fs : ForwardState)
      (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let rules ← rs.applicableForwardRules (← h.getType)
    let patInsts ← rs.forwardRulePatternSubstsInLocalDecl (← h.getDecl)
    fs.addHypWithPatSubstsCore ruleMatches diff.newGoal h rules patInsts

  updateTarget (fs : ForwardState) (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let patInsts ←
      rs.forwardRulePatternSubstsInExpr (← diff.newGoal.getType)
    fs.updateTargetPatSubstsCore ruleMatches diff.newGoal patInsts

  updateHypTypes (hypTypes : PHashSet RPINF) : BaseM (PHashSet RPINF) := do
    let mut hypTypes := hypTypes
    for fvarId in diff.removedFVars do
      let type ← diff.oldGoal.withContext do rpinf (← fvarId.getType)
      hypTypes := hypTypes.erase type
    for fvarId in diff.addedFVars do
      let type ← diff.newGoal.withContext do rpinf (← fvarId.getType)
      hypTypes := hypTypes.insert type
    return hypTypes

end Aesop
