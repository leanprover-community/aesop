/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.UScript
import Aesop.Script.UScriptToSScript
import Aesop.Script.Util
import Aesop.Script.SScript
import Aesop.Tracing

open Lean Lean.Meta

namespace Aesop.Script

private def goalsToMessageData (state : Meta.SavedState) (goals : Array MVarId) :
    MetaM MessageData :=
  state.runMetaM' do
    addMessageContext $
    MessageData.joinSep
      (goals.map λ g => m!"?{g.name}:{indentD $ toMessageData g}").toList
      "\n"

namespace DynStructureM

structure Context where
  /-- The tactic invocation steps corresponding to the original unstructured
  script, but with `MVarId` keys adjusted to fit the current `MetaM` state. This
  state evolves during dynamic structuring and we continually update the `steps`
  so that this map's keys refer to metavariables which exist in the current
  `MetaM` state. -/
  steps : PHashMap MVarId (Nat × Step)
  deriving Inhabited

structure State where
  perfect : Bool := true

/--
Given a bijective map `map` from new `MVarId`s to old `MVarId`s, update the
`steps` of the context `c` such that each entry whose key is an old `MVarId` `m`
is replaced with an entry whose key is the corresponding new `MVarId`
`map⁻¹ m`.
-/
def Context.updateMVarIds (c : Context) (map : Std.HashMap MVarId MVarId) :
    Context :=
  let steps := map.fold (init := c.steps) λ steps newMVarId oldMVarId =>
    if let (some step) := steps.find? oldMVarId then
      steps.erase oldMVarId |>.insert newMVarId step
    else
      steps
  { c with steps }

end DynStructureM

abbrev DynStructureM :=
  ReaderT DynStructureM.Context $ StateRefT DynStructureM.State MetaM

def DynStructureM.run (x : DynStructureM α) (script : UScript) :
    MetaM (α × Bool) := do
  let mut steps : PHashMap MVarId (Nat × Step) := {}
  for h : i in [:script.size] do
    let step := script[i]'h.2
    steps := steps.insert step.preGoal (i, step)
  let (a, s) ← ReaderT.run x { steps } |>.run {}
  return (a, s.perfect)

def withUpdatedMVarIds
    (oldPostState newPostState : Meta.SavedState)
    (oldPostGoals newPostGoals : Array MVarId) (onFailure : DynStructureM α)
    (onSuccess : DynStructureM α) : DynStructureM α := do
  match ← matchGoals newPostState oldPostState newPostGoals oldPostGoals with
  | some m => withReader (·.updateMVarIds m) onSuccess
  | none => onFailure

structure DynStructureResult where
  script : List Step
  postState : Meta.SavedState

partial def structureDynamicCore (preState : Meta.SavedState) (preGoal : MVarId)
    (uscript : UScript) : MetaM (Option (UScript × Bool)) :=
  withAesopTraceNode .script (λ r => return m!"{exceptOptionEmoji r} Dynamically structuring the script") do
    aesop_trace[script] "unstructured script:{indentD $ MessageData.joinSep (uscript.map toMessageData |>.toList) "\n"}"
    let (result?, perfect) ← go preState #[preGoal] |>.run uscript
    let some result := result?
      | return none
    return some (result.script.toArray, perfect)
where
  go (preState : Meta.SavedState) (preGoals : Array MVarId) :
      DynStructureM (Option DynStructureResult) :=
    withIncRecDepth do
    if h : 0 < preGoals.size then
      -- Try to apply the step for the main goal, then solve the remaining goals.
      let firstGoal := preGoals[0]
      let result? ← withAesopTraceNode .script (λ r => return m!"{exceptOptionEmoji r} Focusing main goal {firstGoal.name}") do
        aesop_trace[script] "goal: {firstGoal.name}{← preState.runMetaM' $ addMessageContext $ indentD firstGoal}"
        goStructured preState preGoals preGoals[0]
      match result? with
      | some result => return result
      | none =>
        -- If this fails, apply the chronologically next step and solve the remaining goals.
        modify ({ · with perfect := false })
        withAesopTraceNode .script (λ r => return m!"{exceptOptionEmoji r} Applying step to chronologically first goal") do
          goUnstructured preState preGoals
    else
      return some { script := [], postState := preState }

  goStructured (preState : Meta.SavedState) (preGoals : Array MVarId)
      (firstPreGoal : MVarId) : DynStructureM (Option DynStructureResult) := do
    let (some (_, step)) := (← read).steps[firstPreGoal]
      | throwError "aesop: internal error while structuring the script: no step for goal {preGoal.name}:{indentD $ ← preState.runMetaM' $ addMessageContext $ toMessageData preGoal}"
    applyStepAndSolveRemaining preState preGoals firstPreGoal 0 step

  goUnstructured (preState : Meta.SavedState) (preGoals : Array MVarId) :
      DynStructureM (Option DynStructureResult) := do
    let steps := (← read).steps
    let firstStep? := findFirstStep? preGoals (steps[·]) (·.fst)
    let some (goalPos, goal, _, step) := firstStep?
      | throwError "aesop: internal error while structuring the script: no step for any of the visible goals{indentD $ ← goalsToMessageData preState preGoals}"
    aesop_trace[script] "goal: {goal.name}{← preState.runMetaM' $ addMessageContext $ indentD goal}"
    applyStepAndSolveRemaining preState preGoals goal goalPos step

  applyStepAndSolveRemaining (preState : Meta.SavedState)
      (preGoals : Array MVarId) (preGoal : MVarId) (goalPos : Nat)
      (step : Step) : DynStructureM (Option DynStructureResult) := do
    aesop_trace[script] "applying step:{indentD $ toMessageData step}"
    aesop_trace[script] "expected post goals:{indentD $ ← goalsToMessageData step.postState (step.postGoals.map (·.goal))}"
    let (postState, postGoals) ←
      try
        runTacticCapturingPostState step.uTactic preState [preGoal]
      catch e =>
        aesop_trace[script] "tactic failed with error:{indentD e.toMessageData}"
        return none
    let postGoals := postGoals.toArray
    withUpdatedMVarIds step.postState postState (step.postGoals.map (·.goal)) postGoals
      (onFailure := do
        aesop_trace[script] "post goals don't match; actual post goals:{indentD $ ← goalsToMessageData postState postGoals}"
        return none) do
      aesop_trace[script] "post goals match"
      let postGoalsWithMVars ← postState.runMetaM' do
        postGoals.mapM λ goal =>
          return { goal, mvars := ← goal.getMVarDependencies }
      -- We need to construct a new step here because the old step's postState
      -- is equivalent to the new postState *only up to mvar assignments*.
      let step := {
        tactic := step.tactic
        postGoals := postGoalsWithMVars
        preState, preGoal, postState
      }
      let postGoals := preGoals[:goalPos] ++ postGoals ++ preGoals[goalPos+1:]
      let postGoals ← postState.runMetaM' do
        postGoals.filterM λ mvarId =>
          return ! (← mvarId.isAssignedOrDelayedAssigned)
      let some { script := tailScript, postState } ← go postState postGoals
        | return none
      let script := step :: tailScript
      return some { script, postState }

def UScript.toSScriptDynamic (preState : Meta.SavedState) (preGoal : MVarId)
    (uscript : UScript) : MetaM (Option (SScript × Bool)) := do
  let some (uscript, perfect) ← structureDynamicCore preState preGoal uscript
    | return none
  let preGoalMVars ← preState.runMetaM' preGoal.getMVarDependencies
  let tacticState := {
    visibleGoals := #[⟨preGoal, preGoalMVars⟩]
    invisibleGoals := ∅
  }
  return some (← orderedUScriptToSScript uscript tacticState, perfect)

end Aesop.Script
