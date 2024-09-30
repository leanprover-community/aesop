/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
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

namespace Stateful

partial def saturateCore (rs : LocalRuleSet) (goal : MVarId) :
    SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.withContext do
    if (← read).options.forwardMaxDepth?.isSome then
      logWarning "saturate: forwardMaxDepth option currently has no effect when using stateful forward reasoning"
    goal.checkNotAssigned `saturate
    let index := rs.forwardRules
    let mut fs : ForwardState := ∅
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← index.get ldecl.type
      fs ← fs.addHyp goal ldecl.fvarId rules
    go fs goal
where
  go (fs : ForwardState) (goal : MVarId) : ScriptM MVarId := do
    withIncRecDepth do
    goal.withContext do
      if let some (prf, fs) ← fs.popFirstMatch? goal then
        trace[saturate] "goal:{indentD goal}"
        let name ← getUnusedUserName forwardHypPrefix
        let type ← inferType prf
        trace[saturate] "add hyp {name} : {type} := {prf}"
        let hyp := { userName := name, value := prf, type }
        let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
          | unreachable!
        goal.withContext do
          let rules ← rs.forwardRules.get type
          let fs ← fs.addHyp goal hyp rules
          go fs goal
      else
        return goal

end Stateful

def saturateMain (rs : LocalRuleSet) (goal : MVarId) (options : Aesop.Options') :
    MetaM (MVarId × Array Script.LazyStep) := do
  let doSaturate :=
    if aesop.dev.statefulForward.get (← getOptions) then
      Stateful.saturateCore rs goal
    else
      saturateCore rs goal
  doSaturate.run { options } |>.run

def saturate (rs : LocalRuleSet) (goal : MVarId) (options : Aesop.Options') :
    MetaM MVarId := do
  if ! options.generateScript then
    (·.fst) <$> saturateMain rs goal options
  else
    let preState ← saveState
    let tacticState ← Script.TacticState.mkInitial goal
    let preGoal := goal
    let (goal, steps) ← saturateMain rs goal options
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
