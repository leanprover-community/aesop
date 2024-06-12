/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.UScript
import Aesop.Script.SScript
import Aesop.Tracing

open Lean Lean.Meta

namespace Aesop.Script

inductive StepTree where
  | empty
  | node (step : Step) (index : Nat) (children : Array StepTree)
  deriving Nonempty

namespace StepTree

protected partial def toMessageData? : StepTree → Option MessageData
  | empty => none
  | node step index children =>
    if children.isEmpty then
      m!"- {index}: {step}"
    else
      m!"- {index}: {step}{indentD $ MessageData.joinSep (children.filterMap (·.toMessageData?) |>.toList) "\n"}"

protected def toMessageData (t : StepTree) : MessageData :=
  t.toMessageData?.getD "empty"

end StepTree

instance : ToMessageData StepTree :=
  ⟨StepTree.toMessageData⟩

partial def UScript.toStepTree (s : UScript) : StepTree := Id.run do
  let mut preGoalMap : HashMap MVarId (Nat × Step) := ∅
  for h : i in [:s.size] do
    preGoalMap := preGoalMap.insert s[i].preGoal (i, s[i])
  if h : 0 < s.size then
    go preGoalMap s[0].preGoal
  else
    return .empty
where
  go (m : HashMap MVarId (Nat × Step)) (goal : MVarId) : StepTree :=
    if let some (i, step) := m.find? goal then
      .node step i (step.postGoals.map (go m ·.goal))
    else
      .empty

def mergeSortedArrays [Ord α] (as : Array (Array α)) : Array α :=
  -- TODO inefficient
  as.foldl (init := #[]) Array.mergeDedup

def isConsecutiveSequence (ns : Array Nat) : Bool := Id.run do
  if h : 0 < ns.size then
    let mut prev := ns[0]
    for n in ns[1:] do
      if n != prev + 1 then
        return false
      prev := n
  return true

namespace StepTree

partial def focusableGoals (t : StepTree) : HashMap MVarId Nat :=
  go t |>.run ∅ |>.2
where
  go : StepTree → StateM (HashMap MVarId Nat) (Array Nat) -- TODO StateRefT
    | .empty => return #[]
    | .node step i children => do
      let childIndexes := mergeSortedArrays $ ← children.mapM go
      let indexes := #[i] ++ childIndexes
      if isConsecutiveSequence indexes then
        let lastIndex := childIndexes[childIndexes.size - 1]?.getD i
        modify (·.insert step.preGoal lastIndex)
      return indexes

partial def numSiblings (t : StepTree) : HashMap MVarId Nat :=
  go 0 t |>.run ∅ |>.2
where
  go (parentNumGoals : Nat) : StepTree → StateM (HashMap MVarId Nat) Unit -- TODO StateRefT
    | .empty => return
    | .node step _ children => do
      modify (·.insert step.preGoal (parentNumGoals - 1))
      children.forM (go children.size)

end StepTree

partial def orderedUScriptToSScript (uscript : UScript) (tacticState : TacticState) : CoreM SScript :=
  withAesopTraceNode .debug (λ e => return m!"{exceptEmoji e} Converting ordered unstructured script to structured script") do
  aesop_trace[debug] "unstructured script:{indentD $ MessageData.joinSep (uscript.map toMessageData |>.toList) "\n"}"
  let stepTree := uscript.toStepTree
  aesop_trace[debug] "step tree:{indentD $ toMessageData stepTree}"
  let focusable := stepTree.focusableGoals
  let numSiblings := stepTree.numSiblings
  aesop_trace[debug] "focusable goals: {focusable.toArray.map λ (mvarId, n) => (mvarId.name, n)}"
  (·.fst) <$> go focusable numSiblings 0 (uscript.size - 1) tacticState
where
  go (focusable : HashMap MVarId Nat) (numSiblings : HashMap MVarId Nat) (start stop : Nat) (tacticState : TacticState) : CoreM (SScript × TacticState) := do
    if start > stop then
      return (.empty, tacticState)
    if let some step := uscript[start]? then
      aesop_trace[debug] "applying step:{indentD $ toMessageData step}"
      let some siblings := numSiblings[step.preGoal]
        | throwError "aesop: internal error while structuring script: unknown sibling count for goal {step.preGoal.name}"
      aesop_trace[debug] "siblings: {siblings}"
      let innerStop? := focusable[step.preGoal]
      aesop_trace[debug] "focusable: {innerStop?.isSome}"
      aesop_trace[debug] "visible goals: {tacticState.visibleGoals.map (·.goal.name)}"
      let some goalPos := tacticState.getVisibleGoalIndex? step.preGoal
        -- I think his can be `none` if the step is for an mvar that was already
        -- assigned by some other step.
        | return (.empty, tacticState)
      aesop_trace[debug] "goal position: {goalPos}"
      if innerStop?.isNone || siblings == 0 then
        let tacticState ← tacticState.applyStep step
        let (tailScript, tacticState) ← go focusable numSiblings (start + 1) stop tacticState
        return (.onGoal goalPos step tailScript, tacticState)
      else
        let innerStop := innerStop?.get!
        let (nestedScript, tacticState) ←
          tacticState.onGoalM step.preGoal λ tacticState => do
            let tacticState ← tacticState.applyStep step
            let (tailScript, tacticState) ←
              go focusable numSiblings (start + 1) innerStop tacticState
            return (.onGoal 0 step tailScript, tacticState)
        let (tailScript, tacticState) ←
          go focusable numSiblings (innerStop + 1) stop tacticState
        let script := .focusAndSolve goalPos nestedScript tailScript
        return (script, tacticState)
    else
      return (.empty, tacticState)

end Aesop.Script
