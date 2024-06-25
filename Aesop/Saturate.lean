/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Forward
import Aesop.RuleSet
import Aesop.RuleTac
import Aesop.Search.Expansion.Basic

open Lean Lean.Meta

namespace Aesop

def isForwardOrDestructRuleName (n : RuleName) : Bool :=
  n.builder == .forward || n.builder == .destruct

structure SaturateM.Context where
  options : Aesop.Options'

abbrev SaturateM := ReaderT SaturateM.Context MetaM

def getSingleGoal [Monad m] [MonadError m] (o : RuleTacOutput) :
    m (MVarId × Meta.SavedState) := do
  let #[app] := o.applications
    | throwError "rule produced more than one rule application"
  let #[goal] := app.goals
    | throwError "rule did not produce exactly one subgoal"
  return (goal, app.postState)

initialize
  registerTraceClass `saturate

partial def saturate (rs : LocalRuleSet) (goal : MVarId) : SaturateM MVarId :=
  withExceptionPrefix "saturate: internal error: " do
  goal.checkNotAssigned `saturate
  go goal
where
  go (goal : MVarId) : SaturateM MVarId :=
    withIncRecDepth do
    trace[saturate] "goal:{indentD goal}"
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
      SaturateM (Option MVarId) := do
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
      let (goal, postState) ← getSingleGoal output
      postState.restore
      return goal

  runFirstRule {α} (goal : MVarId) (mvars : UnorderedArraySet MVarId)
      (preState : Meta.SavedState)
      (matchResults : Array (IndexMatchResult (Rule α))) :
      SaturateM (Option MVarId) := do
    for matchResult in matchResults do
      if let some goal ← runRule goal mvars preState matchResult then
        return some goal
    return none

end Aesop
