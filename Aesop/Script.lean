/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.EqualUpToIds
import Aesop.Script.ScriptBuilder
import Aesop.Script.TacticState
import Batteries.Lean.Meta.Clear
import Batteries.Lean.Meta.Inaccessible
import Batteries.Lean.HashSet
import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.SeqFocus

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop

variable [Monad m] [MonadError m] [MonadQuotation m]

@[inline]
private def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1

structure TacticInvocation where
  preState : Meta.SavedState
  preGoal : MVarId
  tacticSeq : Array Syntax.Tactic
  postGoals : Array GoalWithMVars
  postState : Meta.SavedState
  deriving Nonempty

def TacticState.applyTacticInvocation (tacticState : TacticState)
    (ti : TacticInvocation) : m TacticState :=
  tacticState.applyTactic ti.preGoal ti.postGoals ti.postState.meta.mctx

namespace TacticInvocation

def noop (preGoal : MVarId) (postGoal : GoalWithMVars)
    (preState postState : Meta.SavedState) : TacticInvocation := {
  tacticSeq := #[]
  postGoals := #[postGoal]
  preGoal, preState, postState
}

def render (acc : Array Syntax.Tactic) (ti : TacticInvocation)
    (tacticState : TacticState) : m (Array Syntax.Tactic × TacticState) := do
  if ti.tacticSeq.size == 0 then
    let tacticState ← tacticState.applyTacticInvocation ti
    return (acc, tacticState)
  else
    let pos ← tacticState.getVisibleGoalIndex ti.preGoal
    let tacticState ← tacticState.applyTacticInvocation ti
    if pos == 0 then
      return (acc ++ ti.tacticSeq, tacticState)
    else
      let posLit := mkOneBasedNumLit pos
      let t ← `(tactic| on_goal $posLit:num => $(ti.tacticSeq):tactic*)
      return (acc.push t, tacticState)

def validate (ti : TacticInvocation) : MetaM Unit := do
  let preMCtx := ti.preState.meta.mctx
  let expectedPostMCtx := ti.postState.meta.mctx
  let expectedPostGoals := ti.postGoals |>.map (·.goal)
  let tac ← `(Lean.Parser.Tactic.tacticSeq| $ti.tacticSeq*)
  let (actualPostState, actualPostGoals) ←
    try
      runTacticMCapturingPostState (evalTactic tac) ti.preState [ti.preGoal]
    catch e =>
      throwError "tactic{indentD tac}\nfailed with error{indentD e.toMessageData}"
  let actualPostGoals := actualPostGoals.toArray
  unless ← tacticStatesEqualUpToIds preMCtx expectedPostMCtx
      actualPostState.meta.mctx expectedPostGoals actualPostGoals do
    throwError "tactic{indentD tac}\nsucceeded but did not generate expected state. Initial goal:{indentD $ ← fmtGoals ti.preState #[ti.preGoal]}\nExpected goals:{indentD $ ← fmtGoals ti.postState $ ti.postGoals.map (·.goal)}\nActual goals:{indentD $ ← fmtGoals actualPostState actualPostGoals}"
where
  fmtGoals (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $
        MessageData.joinSep (← goals.mapM (λ g => return m!"{g}")).toList "\n"

end TacticInvocation


abbrev UnstructuredScript := Array TacticInvocation

def UnstructuredScript.render (tacticState : TacticState)
    (s : UnstructuredScript) : m (Array Syntax.Tactic) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState := tacticState
  for ti in s do
    let (script', tacticState') ← ti.render script tacticState
    script := script'
    tacticState := tacticState'
  return script

def UnstructuredScript.validate (s : UnstructuredScript) : MetaM Unit :=
  s.forM (·.validate)


inductive StructuredScript
  | empty
  | unstructuredStep (ti : TacticInvocation) (tail : StructuredScript)
  | solve (goal : MVarId) (here tail : StructuredScript)
  deriving Inhabited

def StructuredScript.render (tacticState : TacticState)
    (script : StructuredScript) : m (Array Syntax.Tactic) := do
  (·.fst) <$> go #[] tacticState script
  where
    go (script : Array Syntax.Tactic) (tacticState : TacticState) :
        StructuredScript → m (Array Syntax.Tactic × TacticState)
      | empty =>
        return (script, tacticState)
      | unstructuredStep ti tail => do
        let (script, tacticState) ← ti.render script tacticState
        go script tacticState tail
      | solve goal here tail => do
        let pos ← tacticState.getVisibleGoalIndex goal
        let (nestedScript, tacticState) ←
          tacticState.onGoalM goal λ ts => do
            let (nestedScript, nestedTacticState) ← go #[] ts here
            if ! nestedTacticState.hasNoVisibleGoals then
              throwError "expected script to solve the goal"
            pure (nestedScript, nestedTacticState)
        let t ←
          if pos == 0 then
            `(tactic| · $[$nestedScript:tactic]*)
          else
            let posLit := mkOneBasedNumLit pos
            `(tactic| on_goal $posLit:num => { $nestedScript:tactic* })
        go (script.push t) tacticState tail

-- TODO resolve positions as part of this step?
-- TODO We currently assume that we completely solve the tactic state. If we
-- don't, we have to allow getStep to fail and leave the goal alone.
partial def UnstructuredScript.toStructuredScript (tacticState : TacticState)
    (script : UnstructuredScript) : m StructuredScript := do
  let mut steps := {}
  for h : i in [:script.size] do
    let step := script[i]'h.2
    steps := steps.insert step.preGoal (i, step)
  (·.fst) <$> go steps tacticState
where
  go (steps : HashMap MVarId (Nat × TacticInvocation))
      (tacticState : TacticState) : m (StructuredScript × TacticState) := do
    if tacticState.hasNoVisibleGoals then
      return (.empty, tacticState)
    else if tacticState.hasSingleVisibleGoal ||
            tacticState.visibleGoalsHaveMVars then
      -- TODO If the original order happens to solve the main goal, we can
      -- structure opportunistically.
      let mut firstStep? := none
      for g in tacticState.visibleGoals do
        if let (some (i, step)) := steps[g.goal] then
          if let some (j, firstStep) := firstStep? then
            firstStep? := some $ if i < j then (i, step) else (j, firstStep)
          else
            firstStep? := some (i, step)
        else
          -- It's possible that a visible goal is solved as a side effect of
          -- some unrelated step. So we can't expect every visible goal to have
          -- an associated step.
          continue
      let some (_, firstStep) := firstStep?
        | throwError "internal error: found no step to solve any visible goal"
      let tacticState ← tacticState.applyTacticInvocation firstStep
      let (tailScript, tacticState) ← go steps tacticState
      return (.unstructuredStep firstStep tailScript, tacticState)
    else
      let mut tacticState := tacticState
      let mut nestedScripts := Array.mkEmpty tacticState.visibleGoals.size
      -- The following loop is not equivalent to a for loop because some of
      -- the later visible goals may be solved while solving an earlier visible
      -- goal.
      while h : tacticState.visibleGoals.size > 0 do
        let goal := tacticState.visibleGoals[0]
        let (nestedScript, nestedTacticState) ←
          tacticState.onGoalM goal.goal λ tacticState => go steps tacticState
        nestedScripts := nestedScripts.push (goal.goal, nestedScript)
        tacticState := nestedTacticState
      let script := nestedScripts.foldr (init := .empty)
        λ (goal, nestedScript) tail => .solve goal nestedScript tail
      return (script, tacticState)

end Aesop
