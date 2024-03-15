/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Forward
import Aesop.RuleSet
import Aesop.RuleTac
import Aesop.Script.Main
import Aesop.Search.Expansion.Basic

open Lean Lean.Meta

namespace Aesop

def isForwardOrDestructRuleName (n : RuleName) : Bool :=
  n.builder == .forward || n.builder == .destruct

structure SaturateM.Context where
  options : Aesop.Options'

abbrev SaturateM := ReaderT SaturateM.Context ScriptM

def getSingleGoal [Monad m] [MonadError m] (o : RuleTacOutput) :
    m (MVarId × Meta.SavedState × Option (Array Script.LazyStep)) := do
  let #[app] := o.applications
    | throwError "rule produced more than one rule application"
  let #[goal] := app.goals
    | throwError "rule did not produce exactly one subgoal"
  return (goal.mvarId, app.postState, app.scriptSteps?)

initialize
  registerTraceClass `saturate

partial def saturateCore (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.checkNotAssigned `saturate
  go goal
where
  go (goal : MVarId) : SaturateM MVarId :=
    withIncRecDepth do
    trace[saturate] "goal {goal.name}:{indentD goal}"
    let mvars := UnorderedArraySet.ofHashSet $ ← goal.getMVarDependencies
    let preState ← show MetaM _ from saveState
    let normMatchResults ← rs.applicableNormalizationRulesWith goal
      (include? := (isForwardOrDestructRuleName ·.name))
    if let some goal ← runFirstRule goal mvars preState normMatchResults then
      return ← go goal
    else
      let safeMatchResults ← rs.applicableSafeRulesWith goal
        (include? := (isForwardOrDestructRuleName ·.name))
      if let some goal ← runFirstRule goal mvars preState safeMatchResults then
        return ← go goal
      else
        clearForwardImplDetailHyps goal

  runRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (matchResult : IndexMatchResult (Rule α)) :
      SaturateM (Option (MVarId × Option (Array Script.LazyStep))) := do
    trace[saturate] "running rule {matchResult.rule.name}"
    let input := {
      indexMatchLocations := matchResult.locations
      patternInstantiations := matchResult.patternInstantiations
      options := (← read).options
      goal, mvars
    }
    let tacResult ←
      runRuleTac matchResult.rule.tac.run matchResult.rule.name preState input
    match tacResult with
    | .inl exc =>
      trace[saturate] "rule failed:{indentD exc.toMessageData}"
      return none
    | .inr output =>
      let (goal, postState, scriptSteps?) ← getSingleGoal output
      postState.restore
      return (goal, scriptSteps?)

  runFirstRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState)
      (matchResults : Array (IndexMatchResult (Rule α))) :
      SaturateM (Option MVarId) := do
    for matchResult in matchResults do
      if let some (goal, scriptSteps?) ← runRule goal mvars preState matchResult then
        if (← read).options.generateScript then
          let some scriptSteps := scriptSteps?
            | throwError "rule '{matchResult.rule.name}' does not support script generation (saturate?)"
          recordScriptSteps scriptSteps
        return some goal
    return none

def saturate (rs : LocalRuleSet) (goal : MVarId) (options : Aesop.Options') :
    MetaM MVarId := do
  if ! options.generateScript then
    (·.fst) <$> (saturateCore rs goal |>.run { options } |>.run)
  else
    let preState ← saveState
    let tacticState ← Script.TacticState.mkInitial goal
    let preGoal := goal
    let (goal, steps) ← saturateCore rs goal |>.run { options } |>.run
    let uscript : Script.UScript ← steps.mapM (·.toStep)
    let tacticSeq ← `(tacticSeq| $(← uscript.render tacticState):tactic*)
    checkRenderedScriptIfEnabled tacticSeq preState preGoal
      (expectCompleteProof := false)
    if options.traceScript then
      addTryThisTacticSeqSuggestion (← getRef) tacticSeq
    return goal

end Aesop
