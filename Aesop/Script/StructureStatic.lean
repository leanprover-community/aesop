import Aesop.Script.UScriptToSScript
import Aesop.Script.Util
import Aesop.Stats.Basic

open Lean Lean.Meta

namespace Aesop.Script

namespace StaticStructureM

structure State where
  perfect : Bool := true

structure Context where
  steps : HashMap MVarId (Nat × Step)

end StaticStructureM

abbrev StaticStructureM :=
  ReaderT StaticStructureM.Context $ StateRefT StaticStructureM.State CoreM

protected def StaticStructureM.run (script : UScript) (x : StaticStructureM α) :
    CoreM (α × Bool) := do
  let mut steps : HashMap MVarId (Nat × Step) := mkHashMap script.size
  for h : i in [:script.size] do
    let step := script[i]'h.2
    if h : step.postGoals.size = 1 then
      if step.postGoals[0].goal == step.preGoal then
        continue
    steps := steps.insert step.preGoal (i, step)
  let (a, s) ← ReaderT.run x { steps } |>.run {}
  return (a, s.perfect)

partial def structureStaticCore (tacticState : TacticState) (script : UScript) :
    CoreM (UScript × Bool) :=
  withConstAesopTraceNode .debug (return m!"statically structuring the tactic script") do
  aesop_trace[debug] "unstructured script:{indentD $ MessageData.joinSep (script.toList.map λ step => m!"{step}") "\n"}"
  let ((script, _), perfect) ← go tacticState |>.run script
  return (script.toArray, perfect)
where
  go (tacticState : TacticState) : StaticStructureM (List Step × TacticState) :=
    withIncRecDepth do
    if let some goal := tacticState.visibleGoals[0]? then
      let step ← nextStep tacticState goal
      aesop_trace[debug] "rendering step:{indentD $ toMessageData step}"
      let tacticState ← tacticState.applyStep step
      let (tailScript, tacticState) ← go tacticState
      return (step :: tailScript, tacticState)
    else
      return ([], tacticState)

  nextStep (tacticState : TacticState) (mainGoal : GoalWithMVars) :
      StaticStructureM Step := do
    let steps := (← read).steps
    if mainGoal.mvars.isEmpty then
      if let some (_, step) := steps[mainGoal.goal] then
        return step
    modify ({· with perfect := false })
    let firstStep? :=
      findFirstStep? tacticState.visibleGoals (steps[·.goal]) (·.fst)
    let some (_, _, _, firstStep) := firstStep?
      | throwError "aesop: internal error while structuring script: no script step found for any of the goals {tacticState.visibleGoals.map (·.goal.name)}"
    return firstStep

def UScript.toSScriptStatic (tacticState : TacticState) (uscript : UScript) :
    CoreM (SScript × Bool) := do
  let (script, perfect) ← structureStaticCore tacticState uscript
  return (← orderedUScriptToSScript script tacticState, perfect)

end Aesop.Script
