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
def ForwardState.applyGoalDiff (rs : LocalRuleSet)
    (diff : GoalDiff) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) := do
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
    return fs.eraseHyp h (← rpinf (← h.getType))

  addHyp (h : FVarId) (fs : ForwardState)
      (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let rules ← rs.applicableForwardRules (← h.getType)
    let patInsts ← rs.forwardRulePatternInstantiationsInLocalDecl (← h.getDecl)
    fs.addHypWithPatInstsCore ruleMatches diff.newGoal h rules patInsts

  updateTarget (fs : ForwardState) (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let patInsts ←
      rs.forwardRulePatternInstantiationsInExpr (← diff.newGoal.getType)
    fs.updateTargetPatInstsCore ruleMatches diff.newGoal patInsts

end Aesop
