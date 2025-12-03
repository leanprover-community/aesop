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
  profilingForwardState do
  goal.withContext do
    if ! aesop.dev.statefulForward.get (← getOptions) then
      return (∅, #[])
    let mut fs : ForwardState := ∅
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← rs.applicableForwardRules ldecl.type
      let patInsts ← rs.forwardRulePatternSubstsInLocalDecl ldecl
      fs := fs.enqueueHypWithPatSubsts ldecl.fvarId rules patInsts
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← goal.getType)
    fs := fs.enqueueTargetPatSubsts patInsts
    let ruleMatches := rs.constForwardRuleMatches
    aesop_trace[forward] do
      for m in ruleMatches do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    return (fs, ruleMatches)

end Aesop.LocalRuleSet
