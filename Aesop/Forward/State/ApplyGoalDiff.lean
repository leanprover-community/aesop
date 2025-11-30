/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Forward.State
public import Aesop.RuleSet

public section

namespace Aesop

open Lean Lean.Meta

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. -/
def ForwardState.applyGoalDiff (rs : LocalRuleSet) (diff : GoalDiff)
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) :=
  profilingForwardState do
  if ! aesop.dev.statefulForward.get (← getOptions) then
    return (fs, #[])
  let fs ← diff.oldGoal.withContext do
    diff.removedFVars.foldM (init := fs) λ fs h => eraseHyp h fs
  diff.newGoal.withContext do
    let (fs, ruleMatches) ←
      diff.addedFVars.foldM (init := (fs, ∅)) λ (fs, ruleMatches) h =>
        addHyp h fs ruleMatches
    if diff.targetChanged then
      updateTarget fs ruleMatches
    else
      return (fs, ruleMatches)
where
  eraseHyp (h : FVarId) (fs : ForwardState) : BaseM ForwardState :=
    withConstAesopTraceNode .forward (return m!"erase hyp {Expr.fvar h} ({h.name})") do
      return fs.eraseHyp h

  addHyp (h : FVarId) (fs : ForwardState)
      (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let rules ← rs.applicableForwardRules (← h.getType)
    let patInsts ← rs.forwardRulePatternSubstsInLocalDecl (← h.getDecl)
    fs.addHypWithPatSubstsCore ruleMatches diff.newGoal h rules patInsts

  updateTarget (fs : ForwardState) (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← diff.newGoal.getType)
    fs.updateTargetPatSubstsCore ruleMatches diff.newGoal patInsts

end Aesop
