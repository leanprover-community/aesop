/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State.ApplyGoalDiff
import Aesop.Forward.State.Initial
import Aesop.RuleSet
import Aesop.RuleTac
import Aesop.Search.Expansion.Basic
import Aesop.Script.Check
import Batteries.Data.BinomialHeap.Basic

open Lean Lean.Meta
open Batteries (BinomialHeap)

namespace Aesop

def isForwardOrDestructRuleName (n : RuleName) : Bool :=
  n.builder == .forward || n.builder == .destruct

structure SaturateM.Context where
  options : Aesop.Options'
  deriving Inhabited

structure SaturateM.State where
  rulePatternCache : RulePatternCache := {}
  rpinfCache : RPINFCache := ∅
  deriving Inhabited

abbrev SaturateM :=
  ReaderT SaturateM.Context $ StateRefT SaturateM.State $ ScriptT BaseM

namespace SaturateM

def run (options : Aesop.Options') (x : SaturateM α) :
    MetaM (α × Array Script.LazyStep) :=
  (·.fst) <$> (ReaderT.run x { options } |>.run' {} |>.run.run)

end SaturateM

def getSingleGoal [Monad m] [MonadError m] (o : RuleTacOutput) :
    m (GoalDiff × Meta.SavedState × Option (Array Script.LazyStep)) := do
  let #[app] := o.applications
    | throwError "rule produced more than one rule application"
  let #[goal] := app.goals
    | throwError "rule did not produce exactly one subgoal"
  return (goal.diff, app.postState, app.scriptSteps?)

initialize
  registerTraceClass `saturate

partial def saturateCore (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.checkNotAssigned `saturate
  go goal
where
  go (goal : MVarId) : SaturateM MVarId :=
    withIncRecDepth do
    checkSystem "saturate"
    trace[saturate] "goal {goal.name}:{indentD goal}"
    let mvars := UnorderedArraySet.ofHashSet $ ← goal.getMVarDependencies
    let preState ← show MetaM _ from saveState
    if let some newGoal ← tryNormRules goal mvars preState then
      go newGoal
    else if let some newGoal ← trySafeRules goal mvars preState then
      go newGoal
    else
      clearForwardImplDetailHyps goal

  tryNormRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) : SaturateM (Option MVarId) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying normalisation rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting normalisation rules") do
        rs.applicableNormalizationRulesWith ∅ goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults

  trySafeRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) : SaturateM (Option MVarId) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying safe rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting safe rules") do
        rs.applicableSafeRulesWith ∅ goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults

  runRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (matchResult : IndexMatchResult (Rule α)) :
      SaturateM (Option (GoalDiff × Option (Array Script.LazyStep))) := do
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} running rule {matchResult.rule.name}") do
    let input := {
      indexMatchLocations := matchResult.locations
      patternSubsts? := matchResult.patternSubsts?
      options := (← read).options
      goal, mvars
    }
    let tacResult ←
      runRuleTac matchResult.rule.tac.run matchResult.rule.name preState input
    match tacResult with
    | .error exc =>
      trace[saturate] exc.toMessageData
      return none
    | .ok output =>
      let (diff, postState, scriptSteps?) ← getSingleGoal output
      postState.restore
      return (diff, scriptSteps?)

  runFirstRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState)
      (matchResults : Array (IndexMatchResult (Rule α))) :
      SaturateM (Option MVarId) := do
    for matchResult in matchResults do
      let ruleResult? ← runRule goal mvars preState matchResult
      if let some (diff, scriptSteps?) := ruleResult? then
        if (← read).options.generateScript then
          let some scriptSteps := scriptSteps?
            | throwError "rule '{matchResult.rule.name}' does not support script generation (saturate?)"
          recordScriptSteps scriptSteps
        return some diff.newGoal
    return none

namespace Stateful

abbrev Queue := BinomialHeap ForwardRuleMatch ForwardRuleMatch.le

partial def saturateCore (rs : LocalRuleSet) (goal : MVarId)
    (options : Options') : SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.withContext do
    goal.checkNotAssigned `saturate
    let (fs, ruleMatches₁) ← rs.mkInitialForwardState goal
    let (fs, ruleMatches₂) ← fs.progressToPhase .norm rs
    let (fs, ruleMatches₃) ← fs.progressToPhase .safe rs
    let queue :=
      (ruleMatches₁ ++ ruleMatches₂ ++ ruleMatches₃).foldl (init := ∅) λ queue m =>
        queue.insert m
    go ∅ fs queue ∅ goal
where
  go (hypDepths : Std.HashMap FVarId Nat) (fs : ForwardState) (queue : Queue)
      (erasedHyps : Std.HashSet FVarId) (goal : MVarId) : SaturateM MVarId := do
    withIncRecDepth do
    checkSystem "saturate"
    goal.withContext do
      if let some (m, queue) := queue.deleteMin then
        if m.rule.name.phase == .unsafe || m.anyHyp erasedHyps.contains then
          return ← go hypDepths fs queue erasedHyps goal
        trace[saturate] "goal:{indentD goal}"
        let some (goal, hyp, removedHyps) ← m.apply goal
          | return ← go hypDepths fs queue erasedHyps goal
        goal.withContext do
          -- TODO use applyGoalDiff
          let fs := removedHyps.foldl (init := fs) λ fs h => fs.eraseHyp h
          let type ← hyp.getType
          let erasedHyps := erasedHyps.insertMany removedHyps
          let mut depth := 0
          let mut hypDepths := hypDepths
          let maxDepth? := options.forwardMaxDepth?
          if maxDepth?.isSome then
            depth := 1 + m.foldHyps (init := 0) λ depth h =>
              max depth (hypDepths[h]?.getD 0)
            hypDepths := hypDepths.insert hyp depth
          trace[saturate] "added hyp (depth {depth}) {Expr.fvar hyp} : {type}"
          if maxDepth?.isSome && depth ≥ maxDepth?.get! then
            go hypDepths fs queue erasedHyps goal
          else
            let (fs, queue) ← addHyp goal (← hyp.getDecl) fs .norm queue
            let (fs, queue) ← addHyp goal (← hyp.getDecl) fs .safe queue
            go hypDepths fs queue erasedHyps goal
      else
        return goal

  addHyp (goal : MVarId) (hypDecl : LocalDecl) (fs : ForwardState)
      (phase : PhaseName) (queue : Queue) : SaturateM (ForwardState × Queue) := do
    let rules ← rs.applicableForwardRules hypDecl.type phase
    let patInsts ← rs.forwardRulePatternSubstsInLocalDecl hypDecl phase
    let (fs, ruleMatches) ←
      fs.addHypWithPatSubsts goal hypDecl.fvarId rules patInsts
    let queue := ruleMatches.foldl (init := queue) λ queue m => queue.insert m
    return (fs, queue)

end Stateful

def saturateMain (rs : LocalRuleSet) (goal : MVarId) (options : Aesop.Options') :
    MetaM (MVarId × Array Script.LazyStep) := do
  let doSaturate :=
    if aesop.dev.statefulForward.get (← getOptions) then
      Stateful.saturateCore rs goal options
    else
      saturateCore rs goal
  doSaturate.run options

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
