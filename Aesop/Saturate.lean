/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleSet
import Aesop.RuleTac
import Aesop.Search.Expansion.Basic
import Aesop.Script.Check

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
    if let some goal ← tryNormRules goal mvars preState then
      return ← go goal
    else if let some goal ← trySafeRules goal mvars preState then
      return ← go goal
    else
      clearForwardImplDetailHyps goal

  tryNormRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) : SaturateM (Option MVarId) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying normalisation rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting normalisation rules") do
        rs.applicableNormalizationRulesWith goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults

  trySafeRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) : SaturateM (Option MVarId) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying safe rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting safe rules") do
        rs.applicableSafeRulesWith goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults

  runRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (matchResult : IndexMatchResult (Rule α)) :
      SaturateM (Option (MVarId × Option (Array Script.LazyStep))) := do
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} running rule {matchResult.rule.name}") do
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
      trace[saturate] exc.toMessageData
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
    let options ← options.toOptions'
    if options.generateScript then
      let uscript : Script.UScript ← steps.mapM (·.toStep)
      let tacticSeq ← `(tacticSeq| $(← uscript.render tacticState):tactic*)
      checkRenderedScriptIfEnabled tacticSeq preState preGoal
        (expectCompleteProof := false)
      if options.traceScript then
        addTryThisTacticSeqSuggestion (← getRef) tacticSeq
    return goal

end Aesop
