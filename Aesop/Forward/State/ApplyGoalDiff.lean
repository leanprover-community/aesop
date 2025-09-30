/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

set_option linter.missingDocs true

namespace Aesop.ForwardState

open Lean Lean.Meta

/-- Given a diff between goals `g₁` and `g₂`, and a forward state `fs` for goal
`g₁`, construct a forward state for `g₂`. Note that you must call
`progressToPhase` to actually process new hypotheses and changes to the
target. -/
def applyGoalDiff (diff : GoalDiff) (fs : ForwardState) :
    BaseM ForwardState := do
  withConstAesopTraceNode .forward (fun _ => return m!"apply goal diff to forward state") do
  aesop_trace[forwardDebug] "old goal:{indentD diff.oldGoal}"
  aesop_trace[forwardDebug] "new goal:{indentD diff.newGoal}"
  -- Erasure is phase-independent (and fairly cheap), so we do it eagerly.
  let mut fs ← diff.oldGoal.withContext do
    diff.removedFVars.foldM (init := fs) λ fs h => do eraseHyp h fs
  if diff.targetMaybeChanged then
    fs := fs.eraseTargetPatSubsts
  return {
    fs with
    hypTypes := ← updateHypTypes fs.hypTypes
    unprocessedNormDiff := fs.unprocessedNormDiff.comp diff
    unprocessedSafeDiff := fs.unprocessedSafeDiff.comp diff
    unprocessedUnsafeDiff := fs.unprocessedUnsafeDiff.comp diff
  }
where
  updateHypTypes (hypTypes : PHashSet RPINF) : BaseM (PHashSet RPINF) := do
    let mut hypTypes := hypTypes
    for fvarId in diff.removedFVars do
      let type ← diff.oldGoal.withContext do rpinf (← fvarId.getType)
      hypTypes := hypTypes.erase type
    for fvarId in diff.addedFVars do
      let type ← diff.newGoal.withContext do rpinf (← fvarId.getType)
      hypTypes := hypTypes.insert type
    return hypTypes

  eraseHyp (h : FVarId) (fs : ForwardState) : BaseM ForwardState :=
    withConstAesopTraceNode .forward (return m!"erase hyp {Expr.fvar h} ({h.name})") do
      return fs.eraseHyp h (← rpinf (← h.getType))

/-- Bring the forward state up to date for the given phase. The returned
forward state accurately represents the partial rule applications of the given
phase and all earlier phases. -/
def progressToPhase (phase : PhaseName) (rs : LocalRuleSet) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) := do
  withConstAesopTraceNode .forward (fun _ => return m!"progressing forward state to phase {phase}") do
  if ! aesop.dev.statefulForward.get (← getOptions) then
    trace[forward] "stateful forward reasoning is disabled"
    return (fs, #[])
  let diff := fs.unprocessedDiff phase
  let fs := {
    fs with
    unprocessedNormDiff := .empty diff.newGoal
    unprocessedSafeDiff := if phase ≥ .safe then .empty diff.newGoal else fs.unprocessedSafeDiff
    unprocessedUnsafeDiff := if phase ≥ .unsafe then .empty diff.newGoal else fs.unprocessedUnsafeDiff
  }
  diff.newGoal.withContext do
    let (fs, ruleMatches) ←
      diff.addedFVars.foldM (init := (fs, ∅)) λ (fs, ruleMatches) h => do
        addHyp h fs diff ruleMatches
    if diff.targetMaybeChanged then
      updateTarget fs diff ruleMatches
    else
      return (fs, ruleMatches)
where
  isRelevantDiff (diff : GoalDiff) : Bool :=
    diff.hasAddedFVars || diff.targetMaybeChanged

  maxPhase : PhaseName := phase
  minPhase : PhaseName :=
    if isRelevantDiff fs.unprocessedNormDiff then
      .norm
    else if isRelevantDiff fs.unprocessedSafeDiff then
      .safe
    else
      .unsafe

  addHyp (h : FVarId) (fs : ForwardState) (diff : GoalDiff)
      (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let rules ← rs.applicableForwardRules (← h.getType) minPhase maxPhase
    let patInsts ←
      rs.forwardRulePatternSubstsInLocalDecl (← h.getDecl) minPhase maxPhase
    fs.addHypWithPatSubstsCore ruleMatches diff.newGoal h rules patInsts

  updateTarget (fs : ForwardState) (diff : GoalDiff)
      (ruleMatches : Array ForwardRuleMatch) :
      BaseM (ForwardState × Array ForwardRuleMatch) := do
    let patInsts ←
      rs.forwardRulePatternSubstsInExpr (← diff.newGoal.getType)
        minPhase maxPhase
    fs.addPatSubstsCore ruleMatches diff.newGoal patInsts

end Aesop.ForwardState
