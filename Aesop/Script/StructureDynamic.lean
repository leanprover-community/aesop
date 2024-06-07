/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.UScript
import Aesop.Script.Util
import Aesop.Script.SScript
import Aesop.Tracing

open Lean Lean.Meta

namespace Aesop.Script


namespace DynStructureM

structure Context where
  /-- The tactic invocation steps corresponding to the original unstructured
  script, but with `MVarId` keys adjusted to fit the current `MetaM` state. This
  state evolves during dynamic structuring and we continually update the `steps`
  so that this map's keys refer to metavariables which exist in the current
  `MetaM` state. -/
  steps : PHashMap MVarId (Nat × Step)
  deriving Inhabited

/--
Given a bijective map `map` from new `MVarId`s to old `MVarId`s, update the
`steps` of the context `c` such that each entry whose key is an old `MVarId` `m`
is replaced with an entry whose key is the corresponding new `MVarId`
`map⁻¹ m`. If any of the old `MVarId`s in `map` do not have a corresponding
entry in `c.steps`, return `none`.
-/
def Context.updateMVarIds (c : Context) (map : HashMap MVarId MVarId) :
    Context :=
  let steps := map.fold (init := c.steps) λ steps newMVarId oldMVarId =>
    if let (some step) := steps.find? oldMVarId then
      steps.erase oldMVarId |>.insert newMVarId step
    else
      steps
  { c with steps }

end DynStructureM

abbrev DynStructureM := ReaderT DynStructureM.Context MetaM

def DynStructureM.run (x : DynStructureM α) (script : UScript) :
    MetaM α := do
  let mut steps : PHashMap MVarId (Nat × Step) := {}
  for h : i in [:script.size] do
    let step := script[i]'h.2
    steps := steps.insert step.preGoal (i, step)
  ReaderT.run x { steps }

def withUpdatedMVarIds
    (oldPostState newPostState : Meta.SavedState)
    (oldPostGoals newPostGoals : Array MVarId) (onFailure : DynStructureM α)
    (onSuccess : DynStructureM α) : DynStructureM α := do
  match ← matchGoals newPostState oldPostState newPostGoals oldPostGoals with
  | some m => withReader (·.updateMVarIds m) onSuccess
  | none => onFailure

-- TODO upstream
local instance [Nonempty α] [Nonempty β] : Nonempty (α × β) :=
  ⟨Classical.ofNonempty, Classical.ofNonempty⟩

structure DynStructureResult where
  script : SScript
  postState : Meta.SavedState
  postGoals : Array MVarId

partial def UScript.toSScriptDynamic
    (preState : Meta.SavedState) (preGoal : MVarId)
    (script : UScript) : MetaM (Option SScript) :=
  withAesopTraceNode .debug (λ r => return m!"{ExceptToEmoji.toEmoji r} structuring generated tactic script") do
    aesop_trace[debug] "unstructured script:{indentD $ tacticsToMessageData $ script.map (·.uTactic)}"
    let (some result) ← go preState #[preGoal] |>.run script
      | return none
    return some result.script
where
  go (preState : Meta.SavedState) (preGoals : Array MVarId) :
      DynStructureM (Option DynStructureResult) := do
    if let some result ← goStructured preState preGoals then
      return some result
    else
      goUnstructured preState preGoals

  -- TODO Array MVarId -> List MVarId?
  -- TODO preState can be implicit in the MetaM state
  goStructured (preState : Meta.SavedState) (preGoals : Array MVarId) :
      DynStructureM (Option DynStructureResult) :=
    withIncRecDepth do
    withAesopTraceNode .debug (collapsed := false) (λ r => return m!"{ExceptToEmoji.toEmoji r} generating structured script") do
      withConstAesopTraceNode .debug (return m!"initial goals:") do
        aesop_trace[debug] ← goalsToMessageData preState preGoals
      if h : preGoals.size > 0 then
        let preGoal := preGoals[0]
        -- Structured mode: if there's only one goal, run the corresponding step...
        if preGoals.size = 1 then
          let (some (_, step)) := (← read).steps[preGoal]
            | throwError "found no step for goal {preGoal.name}:{indentD $ ← preState.runMetaM' do addMessageContext $ toMessageData preGoal}"
          aesop_trace[debug] "running tactic:{indentD step.uTactic}"
          withConstAesopTraceNode .debug (return m!"expected post goals:") do
            aesop_trace[debug] ← goalsToMessageData step.postState $ step.postGoals.map (·.goal)
          let (postState, postGoals) ←
            try
              runTacticCapturingPostState step.uTactic preState preGoals.toList
            catch e =>
              aesop_trace[debug] "tactics failed with error:{indentD e.toMessageData}"
              return none
          let postGoals := postGoals.toArray
          withUpdatedMVarIds step.postState postState
              (step.postGoals.map (·.goal)) postGoals
              (onFailure := do
                aesop_trace[debug] "post goals don't match; actual post goals:{indentD $ ← goalsToMessageData postState postGoals}"
                return none) do
            aesop_trace[debug] "post goals match"
            let some { script := tailScript, postState, postGoals } ←
              goStructured postState postGoals
              | return none
            let script := .onGoal 0 step tailScript
            return some { script, postState, postGoals }
        -- ... otherwise focus and solve the main goal.
        else
          aesop_trace[debug] "entering main goal"
          let some { script := nestedScript, postState, postGoals } ←
            goStructured preState #[preGoal]
            | return none
          let remainingPreGoals ← postState.runMetaM' $
            preGoals[1:].toArray.filterM λ g =>
              return ! (← g.isAssignedOrDelayedAssigned)
          withConstAesopTraceNode .debug (return m!"remaining goals:") do
            aesop_trace[debug] ← goalsToMessageData preState remainingPreGoals
          let some { script := tailScript, postState, postGoals } ←
            goStructured postState (postGoals ++ remainingPreGoals)
            | return none
          let script := .focusAndSolve 0 nestedScript tailScript
          return some { script, postState, postGoals }
      else
        return some {
          script := .empty
          postState := preState
          postGoals := preGoals
        }

  goUnstructured (preState : Meta.SavedState) (preGoals : Array MVarId) :
      DynStructureM (Option DynStructureResult) :=
    -- Unstructured mode: execute the first step according to the original
    -- order.
    withIncRecDepth do
    withAesopTraceNode .debug (collapsed := false) (λ r => return m!"{ExceptToEmoji.toEmoji r} falling back to unstructured script") do
      let steps := (← read).steps
      let firstStep? := findFirstStep? preGoals (steps[·]) (·.fst)
      let some (goalPos, goal, _, step) := firstStep?
        | throwError "found no step for any of the visible goals{indentD $ ← goalsToMessageData preState preGoals}"
      aesop_trace[debug] "running tactics on goal {goalPos}:{indentD $ step.uTactic}"
      withConstAesopTraceNode .debug (return m!"expected post goals:") do
        aesop_trace[debug] ← goalsToMessageData step.postState $ step.postGoals.map (·.goal)
      let (postState, postGoals) ←
        try
          runTacticCapturingPostState step.uTactic preState [goal]
        catch e =>
          aesop_trace[debug] "tactics failed with error:{indentD e.toMessageData}"
          return none
      let postGoals := postGoals.toArray
      withUpdatedMVarIds step.postState postState
          (step.postGoals.map (·.goal)) postGoals
          (onFailure := do
            aesop_trace[debug] "post goals don't match; actual post goals:{indentD $ ← goalsToMessageData postState postGoals}"
            return none) do
        aesop_trace[debug] "post goals match"
        let postGoals := preGoals[:goalPos] ++ postGoals ++ preGoals[goalPos+1:]
        let some { script := tailScript, postState, postGoals } ←
          go postState postGoals
          | return none
        let script := .onGoal goalPos step tailScript
        return some { script, postState, postGoals }

  goalsToMessageData (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $
        MessageData.joinSep
          (goals.map λ g => m!"?{g.name}:{indentD $ toMessageData g}").toList
          "\n"

end Aesop.Script
