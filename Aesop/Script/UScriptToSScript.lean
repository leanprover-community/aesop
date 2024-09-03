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
    m!"- {index}: {step}{if children.isEmpty then m!"" else indentD $ MessageData.joinSep (children.filterMap (·.toMessageData?) |>.toList) "\n"}"

protected def toMessageData (t : StepTree) : MessageData :=
  t.toMessageData?.getD "empty"

end StepTree

instance : ToMessageData StepTree :=
  ⟨StepTree.toMessageData⟩

partial def UScript.toStepTree (s : UScript) : StepTree := Id.run do
  let mut preGoalMap : Std.HashMap MVarId (Nat × Step) := ∅
  for h : i in [:s.size] do
    preGoalMap := preGoalMap.insert s[i].preGoal (i, s[i])
  if h : 0 < s.size then
    go preGoalMap s[0].preGoal
  else
    return .empty
where
  go (m : Std.HashMap MVarId (Nat × Step)) (goal : MVarId) : StepTree :=
    if let some (i, step) := m[goal]? then
      .node step i (step.postGoals.map (go m ·.goal))
    else
      .empty

def sortDedupArrays [Ord α] (as : Array (Array α)) : Array α :=
  let sz := as.foldl (init := 0) (· + ·.size)
  let as := as.foldl (init := Array.mkEmpty sz) (· ++ ·)
  as.sortDedup

def isConsecutiveSequence (ns : Array Nat) : Bool := Id.run do
  if let some hd := ns[0]? then
    let mut prev := hd
    for n in ns[1:] do
      if n != prev + 1 then
        return false
      prev := n
  return true

namespace StepTree

partial def focusableGoals (t : StepTree) : Std.HashMap MVarId Nat :=
  runST (λ _ => go t |>.run ∅) |>.2
where
  go {σ} : StepTree → StateRefT (Std.HashMap MVarId Nat) (ST σ) (Array Nat)
    | .empty => return #[]
    | .node step i children => do
      let childIndexes := sortDedupArrays $ ← children.mapM go
      let indexes :=
        (Array.mkEmpty $ childIndexes.size + 1).push i ++ childIndexes
      if isConsecutiveSequence indexes then
        let lastIndex := childIndexes[childIndexes.size - 1]?.getD i
        modify (·.insert step.preGoal lastIndex)
      return indexes

partial def numSiblings (t : StepTree) : Std.HashMap MVarId Nat :=
  runST (λ _ => go 0 t |>.run ∅) |>.2
where
  go {σ} (parentNumGoals : Nat) :
      StepTree → StateRefT (Std.HashMap MVarId Nat) (ST σ) Unit
    | .empty => return
    | .node step _ children => do
      modify (·.insert step.preGoal (parentNumGoals - 1))
      children.forM (go children.size)

end StepTree

partial def orderedUScriptToSScript (uscript : UScript) (tacticState : TacticState) : CoreM SScript :=
  withAesopTraceNode .script (λ e => return m!"{exceptEmoji e} Converting ordered unstructured script to structured script") do
  aesop_trace[script] "unstructured script:{indentD $ MessageData.joinSep (uscript.map toMessageData |>.toList) "\n"}"
  let stepTree := uscript.toStepTree
  aesop_trace[script] "step tree:{indentD $ toMessageData stepTree}"
  let focusable := stepTree.focusableGoals
  let numSiblings := stepTree.numSiblings
  aesop_trace[script] "focusable goals: {focusable.toArray.map λ (mvarId, n) => (mvarId.name, n)}"
  (·.fst) <$> go focusable numSiblings 0 (uscript.size - 1) tacticState
where
  go (focusable : Std.HashMap MVarId Nat) (numSiblings : Std.HashMap MVarId Nat)
      (start stop : Nat) (tacticState : TacticState) :
      CoreM (SScript × TacticState) := do
    if start > stop then
      return (.empty, tacticState)
    if let some step := uscript[start]? then
      aesop_trace[script] "applying step:{indentD $ toMessageData step}"
      let some siblings := numSiblings[step.preGoal]?
        | throwError "aesop: internal error while structuring script: unknown sibling count for goal {step.preGoal.name}"
      aesop_trace[script] "siblings: {siblings}"
      let innerStop? := focusable[step.preGoal]?
      aesop_trace[script] "focusable: {innerStop?.isSome}"
      aesop_trace[script] "visible goals: {tacticState.visibleGoals.map (·.goal.name)}"
      let some goalPos := tacticState.getVisibleGoalIndex? step.preGoal
        -- I think his can be `none` if the step is for an mvar that was already
        -- assigned by some other step.
        | return (.empty, tacticState)
      aesop_trace[script] "goal position: {goalPos}"
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
