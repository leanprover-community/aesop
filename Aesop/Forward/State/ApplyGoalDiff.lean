/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

namespace Aesop.ForwardState

open Lean Lean.Meta

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. -/
def applyGoalDiff (rs : LocalRuleSet) (diff : GoalDiff) (fs : ForwardState) :
    BaseM ForwardState :=
  profilingForwardState do
  if ! aesop.dev.statefulForward.get (← getOptions) then
    return fs
  let fs ← diff.oldGoal.withContext do
    diff.removedFVars.foldM (init := fs) λ fs h => eraseHyp h fs
  diff.newGoal.withContext do
    let fs ← diff.addedFVars.foldM (init := fs) λ fs h => addHyp h fs
    if diff.targetChanged then
      updateTarget fs
    else
      return fs
where
  eraseHyp (h : FVarId) (fs : ForwardState) : BaseM ForwardState :=
    withConstAesopTraceNode .forward (return m!"erase hyp {Expr.fvar h} ({h.name})") do
      return fs.eraseHyp h

  addHyp (h : FVarId) (fs : ForwardState) : BaseM ForwardState := do
    let rules ← rs.applicableForwardRules (← h.getType)
    let patInsts ← rs.forwardRulePatternSubstsInLocalDecl (← h.getDecl)
    return fs.enqueueHypWithPatSubsts h rules patInsts

  updateTarget (fs : ForwardState) : BaseM ForwardState := do
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← diff.newGoal.getType)
    return fs.enqueueTargetPatSubsts patInsts

end Aesop.ForwardState
