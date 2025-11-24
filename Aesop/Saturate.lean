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

abbrev SaturateM := ReaderT SaturateM.Context <| ScriptT BaseM

namespace SaturateM

def run (options : Aesop.Options') (x : SaturateM α) : MetaM (α × Stats) := do
  let ((a, _), stats) ← ReaderT.run x { options } |>.run.run
  return (a, stats)

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
  -- We use the forward state only to track the hypotheses present in the goal.
  let (fs, _) ← rs.mkInitialForwardState goal
  go goal fs
where
  go (goal : MVarId) (fs : ForwardState) : SaturateM MVarId :=
    withIncRecDepth do
    checkSystem "saturate"
    trace[saturate] "goal {goal.name}:{indentD goal}"
    let mvars := UnorderedArraySet.ofHashSet $ ← goal.getMVarDependencies
    let preState ← show MetaM _ from saveState
    if let some diff ← tryNormRules goal mvars preState fs.hypTypes then
      let (fs, _) ← fs.applyGoalDiff rs diff
      go diff.newGoal fs
    else if let some diff ← trySafeRules goal mvars preState fs.hypTypes then
      let (fs, _) ← fs.applyGoalDiff rs diff
      go diff.newGoal fs
    else
      clearForwardImplDetailHyps goal

  tryNormRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (hypTypes : PHashSet RPINF) :
      SaturateM (Option GoalDiff) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying normalisation rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting normalisation rules") do
        profilingRuleSelection do
        rs.applicableNormalizationRulesWith ∅ goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults hypTypes

  trySafeRules (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (hypTypes : PHashSet RPINF) :
      SaturateM (Option GoalDiff) :=
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} trying safe rules") do
      let matchResults ←
        withTraceNode `saturate (λ res => return m!"{exceptEmoji res} selecting safe rules") do
        profilingRuleSelection do
        rs.applicableSafeRulesWith ∅ goal
          (include? := (isForwardOrDestructRuleName ·.name))
      runFirstRule goal mvars preState matchResults hypTypes

  runRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState) (matchResult : IndexMatchResult (Rule α))
      (hypTypes : PHashSet RPINF) :
      SaturateM (Option (GoalDiff × Option (Array Script.LazyStep))) := do
    withTraceNode `saturate (λ res => return m!"{exceptOptionEmoji res} running rule {matchResult.rule.name}") do
    profilingRule matchResult.rule.name (·.isSome) do
    let input := {
      indexMatchLocations := matchResult.locations
      patternSubsts? := matchResult.patternSubsts?
      options := (← read).options
      hypTypes, goal, mvars
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
      (matchResults : Array (IndexMatchResult (Rule α)))
      (hypTypes : PHashSet RPINF) : SaturateM (Option GoalDiff) := do
    for matchResult in matchResults do
      let ruleResult? ← runRule goal mvars preState matchResult hypTypes
      if let some (diff, scriptSteps?) := ruleResult? then
        if (← read).options.generateScript then
          let some scriptSteps := scriptSteps?
            | throwError "rule '{matchResult.rule.name}' does not support script generation (saturate?)"
          recordScriptSteps scriptSteps
        return some diff
    return none

namespace Stateful

abbrev Queue := BinomialHeap ForwardRuleMatch ForwardRuleMatch.le

partial def saturateCore (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.withContext do
    goal.checkNotAssigned `saturate
    let (fs, ruleMatches) ← rs.mkInitialForwardState goal
    let queue := ruleMatches.foldl (init := ∅) λ queue m => queue.insert m
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
        let oldGoal := goal
        let some (goal, hyp, removedHyps) ← profilingRule m.rule.name (·.isSome) do
          m.apply goal (skip? := some (fs.hypTypes.contains ·))
          | return ← go hypDepths fs queue erasedHyps goal
        goal.withContext do
          -- TODO use applyGoalDiff
          let fs ← profilingForwardState do
            removedHyps.foldlM (init := fs) λ fs h => do
              let type ← oldGoal.withContext do rpinf (← h.getType)
              return fs.eraseHyp h type
          let type ← hyp.getType
          let erasedHyps := erasedHyps.insertMany removedHyps
          let mut depth := 0
          let mut hypDepths := hypDepths
          let maxDepth? := (← read).options.forwardMaxDepth?
          if maxDepth?.isSome then
            depth := 1 + m.foldHyps (init := 0) λ depth h =>
              max depth (hypDepths[h]?.getD 0)
            hypDepths := hypDepths.insert hyp depth
          trace[saturate] "added hyp (depth {depth}) {Expr.fvar hyp} : {type}"
          if maxDepth?.isSome && depth ≥ maxDepth?.get! then
            go hypDepths fs queue erasedHyps goal
          else
            let rules ← profilingRuleSelection do
              rs.applicableForwardRules type
            let (fs, ruleMatches) ← profilingForwardState do
              let patInsts ←
                rs.forwardRulePatternSubstsInLocalDecl (← hyp.getDecl)
              fs.addHypWithPatSubsts goal hyp rules patInsts
            let queue :=
              ruleMatches.foldl (init := queue) λ queue m => queue.insert m
            go hypDepths fs queue erasedHyps goal
      else
        return goal

end Stateful

def saturateMain' (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId :=
  profiling (fun stats _ total => { stats with total }) do
  let preState ← show MetaM _ from saveState
  let tacticState ←
    if (← read).options.generateScript then
      profiling (fun stats _ n => { stats with script := stats.script + n }) do
      Script.TacticState.mkInitial goal
    else
      pure default -- unused when script generation is disabled
  let preGoal := goal
  let goal ← profiling (fun stats _ search => { stats with search }) do
    if aesop.dev.statefulForward.get (← getOptions) then
      Stateful.saturateCore rs goal
    else
      saturateCore rs goal
  if (← read).options.generateScript then
    let steps ← get
    let tacticSeq ← profiling (fun stats _ n => { stats with script := stats.script + n }) do
      let uscript : Script.UScript ← steps.mapM (·.toStep)
      `(tacticSeq| $(← uscript.render tacticState):tactic*)
    recordScriptGenerated { method := .static, perfect := true, hasMVar := false }
    checkRenderedScriptIfEnabled tacticSeq preState preGoal
      (expectCompleteProof := false)
    if (← read).options.traceScript then
      addTryThisTacticSeqSuggestion (← getRef) tacticSeq
  return goal

def saturateMain (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId := do
  let goal ← saturateMain' rs goal
  let stats ← getStats
  stats.trace .stats
  return goal

def saturate (rs : LocalRuleSet) (goal : MVarId) (options : Aesop.Options') :
    MetaM (MVarId × Stats) := do
  saturateMain rs goal |>.run options

end Aesop
