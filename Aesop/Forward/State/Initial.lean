/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

open Lean Lean.Meta

namespace Aesop.LocalRuleSet

def mkInitialForwardState (goal : MVarId) (rs : LocalRuleSet) :
    BaseM (ForwardState × Array ForwardRuleMatch) := do
  if ! aesop.dev.statefulForward.get (← getOptions) then
    return (default, #[])
  goal.withContext do
    let diff := {
      oldGoal := goal -- HACK this is not accurate, but it doesn't matter for our use cases.
      newGoal := goal
      addedFVars := (← getLCtx).foldl (init := ∅) fun addedFVars ldecl =>
        if ldecl.isImplementationDetail then
          addedFVars
        else
          addedFVars.insert ldecl.fvarId
      removedFVars := ∅
      targetMaybeChanged := true
    }
    let mut fs := {
      ruleStates := .empty
      hyps := .empty
      patSubsts := .empty
      unprocessedNormDiff := diff
      unprocessedSafeDiff := diff
      unprocessedUnsafeDiff := diff
    }
    let ruleMatches := rs.constForwardRuleMatches
    aesop_trace[forward] do
      for m in ruleMatches do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    return (fs, ruleMatches)

end Aesop.LocalRuleSet
