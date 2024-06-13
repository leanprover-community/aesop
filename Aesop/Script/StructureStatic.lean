import Aesop.Script.UScriptToSScript
import Aesop.Script.Util

open Lean Lean.Meta

namespace Aesop.Script

partial def structureStaticCore (tacticState : TacticState) (script : UScript) :
    CoreM UScript :=
  withConstAesopTraceNode .debug (return m!"statically structuring the tactic script") do
  aesop_trace[debug] "unstructured script:{indentD $ MessageData.joinSep (script.toList.map λ step => m!"{step}") "\n"}"
  let mut steps : HashMap MVarId (Nat × Step) := mkHashMap script.size
  for h : i in [:script.size] do
    let step := script[i]'h.2
    if h : step.postGoals.size = 1 then
      if step.postGoals[0].goal == step.preGoal then
        continue
    steps := steps.insert step.preGoal (i, step)
  (·.fst.toArray) <$> go steps tacticState
where
  go (steps : HashMap MVarId (Nat × Step)) (tacticState : TacticState) :
      CoreM (List Step × TacticState) :=
    withIncRecDepth do
    if let some goal := tacticState.visibleGoals[0]? then
      let step ← nextStep steps tacticState goal
      aesop_trace[debug] "rendering step:{indentD $ toMessageData step}"
      let tacticState ← tacticState.applyStep step
      let (tailScript, tacticState) ← go steps tacticState
      return (step :: tailScript, tacticState)
    else
      return ([], tacticState)

  nextStep (steps : HashMap MVarId (Nat × Step)) (tacticState : TacticState)
      (mainGoal : GoalWithMVars) : CoreM Step := do
    if mainGoal.mvars.isEmpty then
      if let some (_, step) := steps[mainGoal.goal] then
        return step
    let firstStep? :=
      findFirstStep? tacticState.visibleGoals (steps[·.goal]) (·.fst)
    let some (_, _, _, firstStep) := firstStep?
      | throwError "aesop: internal error while structuring script: no script step found for any of the goals {tacticState.visibleGoals.map (·.goal.name)}"
    return firstStep

def UScript.toSScriptStatic (tacticState : TacticState) (uscript : UScript) :
    CoreM SScript := do
  let script ← structureStaticCore tacticState uscript
  orderedUScriptToSScript script tacticState

end Aesop.Script
