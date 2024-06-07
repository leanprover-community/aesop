import Aesop.Script.SScript
import Aesop.Script.UScript
import Aesop.Script.Util
import Aesop.Tracing

open Lean Lean.Meta

namespace Aesop.Script

partial def UScript.toSScriptStatic (tacticState : TacticState)
    (script : UScript) : CoreM SScript :=
  withConstAesopTraceNode .debug (return m!"statically structuring the tactic script") do
  aesop_trace[debug] "unstructured script:{indentD $ MessageData.joinSep (script.toList.map λ step => m!"{step}") "\n"}"
  let mut steps : HashMap MVarId (Nat × Step) := mkHashMap script.size
  for h : i in [:script.size] do
    let step := script[i]'h.2
    if h : step.postGoals.size = 1 then
      if step.postGoals[0].goal == step.preGoal then
        continue
    steps := steps.insert step.preGoal (i, step)
  (·.fst) <$> go steps tacticState
where
  go (steps : HashMap MVarId (Nat × Step)) (tacticState : TacticState) :
      CoreM (SScript × TacticState) :=
    withIncRecDepth do
    if tacticState.visibleGoals.isEmpty then
      return (.empty, tacticState)
    else if tacticState.visibleGoals.size == 1 ||
            tacticState.visibleGoalsHaveMVars then
      -- "Unstructured mode"
      -- TODO If the original order happens to solve the main goal, we can
      -- structure opportunistically.
      let firstStep? :=
        findFirstStep? tacticState.visibleGoals (steps.find? ·.goal) (·.fst)
      if let some (goalPos, _, _, firstStep) := firstStep? then
        aesop_trace[debug] "rendering step:{indentD $ toMessageData firstStep}"
        let tacticState ← tacticState.applyStep firstStep
        let (tailScript, tacticState) ← go steps tacticState
        return (.onGoal goalPos firstStep tailScript, tacticState)
      else
        let numVisibleGoals := tacticState.visibleGoals.size
        let tacticState := tacticState.solveVisibleGoals
        return (.sorryN numVisibleGoals, tacticState)
    else
      -- "Structured mode"
      let mut tacticState := tacticState
      let mut nestedScripts := Array.mkEmpty tacticState.visibleGoals.size
      -- The following loop is not equivalent to a for loop because some of
      -- the later visible goals may be solved while solving an earlier visible
      -- goal.
      while h : tacticState.visibleGoals.size > 0 do
        -- TODO is the goal pos not always 0?
        let goal := tacticState.visibleGoals[0]
        let goalPos ← tacticState.getVisibleGoalIndex goal.goal
        let (nestedScript, nestedTacticState) ←
          withConstAesopTraceNode .debug (return m!"visiting goal {goalPos}: {goal.goal.name}") do
            tacticState.onGoalM goal.goal λ tacticState => do
              go steps tacticState
        nestedScripts := nestedScripts.push (goalPos, nestedScript)
        tacticState := nestedTacticState
      let script := nestedScripts.foldr (init := .empty)
        λ (goalPos, nestedScript) tail =>
          .focusAndSolve goalPos nestedScript tail
      return (script, tacticState)

end Aesop.Script
