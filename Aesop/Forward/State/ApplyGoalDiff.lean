/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

namespace Aesop

open Lean Lean.Meta

variable [Monad m] [MonadRulePatternCache m] [MonadControlT MetaM m]
  [MonadLiftT MetaM m]

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. `goal` must be the post-goal of `diff`. -/
def ForwardState.applyGoalDiff (rs : LocalRuleSet) (goal : MVarId)
    (diff : GoalDiff) (fs : ForwardState) :
    m (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    if ! diff.fvarSubst.isEmpty then
      show MetaM _ from throwError "aesop: internal error: non-empty FVarSubst in GoalDiff is currently not supported"
    let mut fs := fs
    let mut ruleMatches := #[]
    for h in diff.removedFVars do
      fs := fs.eraseHyp h
    for h in diff.addedFVars do
      let rules ← rs.applicableForwardRules (← h.getType)
      let patInsts ← rs.forwardRulePatternInstantiationsInLocalDecl (← h.getDecl)
      let (fs', ruleMatches') ←
        fs.addHypWithPatInstsCore ruleMatches goal h rules patInsts
      fs := fs'
      ruleMatches := ruleMatches'
    if diff.targetMaybeChanged then
      let patInsts ← rs.forwardRulePatternInstantiationsInExpr (← goal.getType)
      let (fs', ruleMatches') ←
        fs.updateTargetPatInstsCore ruleMatches goal patInsts
      fs := fs'
      ruleMatches := ruleMatches'
    return (fs, ruleMatches)

end Aesop
