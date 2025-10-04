/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

open Lean Lean.Meta

namespace Aesop.LocalRuleSet

def mkInitialForwardStateForPhase (goal : MVarId) (rs : LocalRuleSet) (phase : PhaseName)
    (forwardState : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    if ! aesop.dev.statefulForward.get (← getOptions) then
      -- We still initialise the hyp types since these are also used by
      -- stateless forward reasoning.
      -- TODO filer
      let mut hypTypes := forwardState.hypTypes
      for ldecl in ← getLCtx do
        if ! ldecl.isImplementationDetail then
          hypTypes := hypTypes.insert (← rpinf ldecl.type)
      return ({ (forwardState : ForwardState) with hypTypes, phaseProgress := phase}, #[])
    let mut fs := {forwardState with phaseProgress := phase}
    let mut rm : Array ForwardRuleMatch := #[]
    rm := rs.constForwardRuleMatches--.filter (·.rule.name.phase == phase)
    aesop_trace[forward] do
      for m in rm do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue

      let rules := (← rs.applicableForwardRules ldecl.type).filter (·.1.name.phase == phase)
      IO.println (rules)
      let patInsts := (← rs.forwardRulePatternSubstsInLocalDecl ldecl)
      IO.println (patInsts.map (·.1))
      let (fs', rm') ←
        fs.addHypWithPatSubstsCore rm goal ldecl.fvarId rules patInsts
      fs := fs'
      rm := rm'
      IO.println (fs.ruleStates.toList.map (·.2.rule))
      IO.println (rm.map (·.rule))
    let patInsts := (← rs.forwardRulePatternSubstsInExpr (← goal.getType))
    -- IO.println (rm.map (·.rule))
    -- IO.println (fs.ruleStates.toList.map (·.1))
    fs.addPatSubstsCore rm goal patInsts

def mkInitialForwardStateForAllPhases (goal : MVarId) (rs : LocalRuleSet) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    if ! aesop.dev.statefulForward.get (← getOptions) then
      -- We still initialise the hyp types since these are also used by
      -- stateless forward reasoning.
      let mut hypTypes := ∅
      for ldecl in ← getLCtx do
        if ! ldecl.isImplementationDetail then
          hypTypes := hypTypes.insert (← rpinf ldecl.type)
      return ({ (∅ : ForwardState) with hypTypes }, #[])
    let mut fs : ForwardState := ∅
    let mut ruleMatches := rs.constForwardRuleMatches
    aesop_trace[forward] do
      for m in ruleMatches do
        aesop_trace![forward] "match for constant rule {m.rule.name}"
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← rs.applicableForwardRules ldecl.type
      let patInsts ← rs.forwardRulePatternSubstsInLocalDecl ldecl
      let (fs', ruleMatches') ←
        fs.addHypWithPatSubstsCore ruleMatches goal ldecl.fvarId rules patInsts
      fs := fs'
      ruleMatches := ruleMatches'
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← goal.getType)
    fs.addPatSubstsCore ruleMatches goal patInsts

def mkInitialForwardStateForPhase? (goal : MVarId) (rs : LocalRuleSet) (phase : Option PhaseName)
    (forwardState : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  match phase with
  | some phase => rs.mkInitialForwardStateForPhase goal phase forwardState
  | none => rs.mkInitialForwardStateForAllPhases goal

def mkInitialForwardState (goal : MVarId) (rs : LocalRuleSet) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  rs.mkInitialForwardStateForPhase? goal none ∅

end Aesop.LocalRuleSet
