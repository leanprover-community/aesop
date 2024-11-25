/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

namespace Aesop

open Lean Lean.Meta

variable [Monad m] [MonadRulePatternCache m] [MonadAlwaysExcept Exception m]
  [MonadRPINF m]

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. -/
-- TODO for some reason compilation is super slow here. Might have something to
-- do with the monad classes, but the issue is not with TC synthesis but with
-- compilation.
def ForwardState.applyGoalDiff (rs : LocalRuleSet)
    (diff : GoalDiff) (fs : ForwardState) :
    m (ForwardState × Array ForwardRuleMatch) :=
  let goal := diff.newGoal
  goal.withContext do
    if ! diff.fvarSubst.isEmpty then
      throwError "aesop: internal error: non-empty FVarSubst in GoalDiff is currently not supported"
    let fs := diff.removedFVars.fold (init := fs) λ fs h => fs.eraseHyp h
    let (fs, ruleMatches) ←
      diff.addedFVars.foldM (init := (fs, ∅)) λ (fs, ruleMatches) h =>
        addHyp goal h fs ruleMatches
    if diff.targetMaybeChanged then
      updateTarget goal fs ruleMatches
    else
      return (fs, ruleMatches)
where
  addHyp (goal : MVarId) (h : FVarId) (fs : ForwardState)
      (ruleMatches : Array ForwardRuleMatch) :
      m (ForwardState × Array ForwardRuleMatch) := do
    let rules ← rs.applicableForwardRules (← h.getType)
    let patInsts ← rs.forwardRulePatternInstantiationsInLocalDecl (← h.getDecl)
    fs.addHypWithPatInstsCore ruleMatches goal h rules patInsts

  updateTarget (goal : MVarId) (fs : ForwardState) (ruleMatches : Array ForwardRuleMatch) :
      m (ForwardState × Array ForwardRuleMatch) := do
    let patInsts ← rs.forwardRulePatternInstantiationsInExpr (← goal.getType)
    fs.updateTargetPatInstsCore ruleMatches goal patInsts

end Aesop
