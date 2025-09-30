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
    BaseM (ForwardState × Array ForwardRuleMatch) :=
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
    -- We must accurately capture the hyp types even if we don't do stateful
    -- forward reasoning since other Aesop systems also rely on them.
    let mut hypTypes := ∅
    for ldecl in ← getLCtx do
      if ! ldecl.isImplementationDetail then
        hypTypes := hypTypes.insert (← rpinf ldecl.type)
    let mut fs := {
      ruleStates := .empty
      hyps := .empty
      patSubsts := .empty
      unprocessedNormDiff := diff
      unprocessedSafeDiff := diff
      unprocessedUnsafeDiff := diff
      hypTypes
    }
    if ! aesop.dev.statefulForward.get (← getOptions) then
      return (fs, #[])
    let ruleMatches := rs.constForwardRuleMatches
    aesop_trace[forward] do
      for m in ruleMatches do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    return (fs, ruleMatches)

end Aesop.LocalRuleSet
