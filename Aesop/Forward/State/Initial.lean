/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

open Lean Lean.Meta

namespace Aesop.LocalRuleSet

def mkInitialForwardState (goal : MVarId) (forwardState : ForwardState) (rs : LocalRuleSet)
    (phase : Option PhaseName) : BaseM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    aesop_trace![forward] "current forward state at begin init: {forwardState}"
    if ! aesop.dev.statefulForward.get (← getOptions) then
      -- We still initialise the hyp types since these are also used by
      -- stateless forward reasoning.
      let mut hypTypes := forwardState.hypTypes
      for ldecl in ← getLCtx do
        if ! ldecl.isImplementationDetail then
          hypTypes := hypTypes.insert (← rpinf ldecl.type)
      -- IO.print "hypTypes: "
      -- IO.println hypTypes.toList
      return ({ forwardState with hypTypes }, #[])
    let mut fs : ForwardState := forwardState
    let mut ruleMatches := rs.constForwardRuleMatches.filter (·.rule.name.phase == phase)
    aesop_trace[forward] do
      for m in ruleMatches do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let mut rules := default
      -- Would it be more efficient to do one filter outside the loop?
      match phase with
      | some phase =>
        rules ← rs.applicableForwardRulesWith ldecl.type (·.name.phase == phase)
      | none => rules ← rs.applicableForwardRules ldecl.type
      let patInsts := ← rs.forwardRulePatternSubstsInLocalDecl ldecl
      let (fs', ruleMatches') ←
        fs.addHypWithPatSubstsCore ruleMatches goal ldecl.fvarId rules patInsts
      fs := {fs' with phaseProgress := phase}
      ruleMatches := ruleMatches'
    -- IO.println "constructing forward state for phase: "
    -- IO.print phase
    -- IO.print "with rules: "
    -- IO.println (fs.ruleStates.toList.map (·.1))
    -- IO.println (ruleMatches.map (·.rule))
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← goal.getType)
    let rs ← fs.addPatSubstsCore ruleMatches goal patInsts
    -- IO.println (rs.1.ruleStates.toList.map (·.1))
    -- IO.println (rs.2.map (·.rule))
    return rs

end Aesop.LocalRuleSet
