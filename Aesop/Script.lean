/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Forward.Basic
import Aesop.Util.Basic
import Aesop.Util.Tactic
import Aesop.Util.EqualUpToIds
import Aesop.Script.ScriptBuilder
import Aesop.Script.TacticState
import Aesop.Tracing
import Batteries.Data.Option
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

def renderOnGoal (acc : Array Syntax.Tactic) (goalPos : Nat)
    (tacticSeq : Array Syntax.Tactic) : m (Array Syntax.Tactic) := do
  if goalPos == 0 then
    return acc ++ tacticSeq
  else
    let posLit := mkOneBasedNumLit goalPos
    let t ← `(tactic| on_goal $posLit:num => $tacticSeq:tactic*)
    return acc.push t

-- Without {α β : Type} universe inference goes haywire.
@[specialize]
def findFirstStep? {α β : Type} (goals : Array α) (step? : α → Option β)
     (stepOrder : β → Nat) : Option (Nat × α × β) := Id.run do
  let mut firstStep? := none
  for h : pos in [:goals.size] do
    let g := goals[pos]'h.2
    if let some step := step? g then
      if let some (_, _, currentFirstStep) := firstStep? then
        if stepOrder step < stepOrder currentFirstStep then
          firstStep? := some (pos, g, step)
      else
        firstStep? := some (pos, g, step)
    else
      continue
  return firstStep?


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
    let acc ← renderOnGoal acc pos ti.tacticSeq
    return (acc, tacticState)

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
  | onGoal (goalPos : Nat) (ti : TacticInvocation) (tail : StructuredScript)
  | focusAndSolve (goalPos : Nat) (here tail : StructuredScript)
  deriving Inhabited

def StructuredScript.render (script : StructuredScript) :
    m (Array Syntax.Tactic) := do
  go #[] script
  where
    go (acc : Array Syntax.Tactic) :
        StructuredScript → m (Array Syntax.Tactic)
      | empty => return acc
      | onGoal goalPos ti tail => do
        let script ← renderOnGoal acc goalPos ti.tacticSeq
        go script tail
      | focusAndSolve goalPos here tail => do
        let nestedScript ← go #[] here
        let t ←
          if goalPos == 0 then
            `(tactic| · $[$nestedScript:tactic]*)
          else
            let posLit := mkOneBasedNumLit goalPos
            `(tactic| on_goal $posLit:num => { $nestedScript:tactic* })
        go (acc.push t) tail

partial def UnstructuredScript.toStructuredScriptStatic
    (tacticState : TacticState) (script : UnstructuredScript) :
    m StructuredScript := do
  let mut steps : HashMap MVarId (Nat × TacticInvocation) := {}
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
      -- "Unstructured mode"
      -- TODO If the original order happens to solve the main goal, we can
      -- structure opportunistically.
      let firstStep? :=
        findFirstStep? tacticState.visibleGoals (steps.find? ·.goal) (·.fst)
      let some (goalPos, _, _, firstStep) := firstStep?
        | throwError "internal error: found no step to solve any visible goal"
      let tacticState ← tacticState.applyTacticInvocation firstStep
      let (tailScript, tacticState) ← go steps tacticState
      return (.onGoal goalPos firstStep tailScript, tacticState)
    else
      -- "Structured mode"
      let mut tacticState := tacticState
      let mut nestedScripts := Array.mkEmpty tacticState.visibleGoals.size
      -- The following loop is not equivalent to a for loop because some of
      -- the later visible goals may be solved while solving an earlier visible
      -- goal.
      while h : tacticState.visibleGoals.size > 0 do
        let goal := tacticState.visibleGoals[0]
        let goalPos ← tacticState.getVisibleGoalIndex goal.goal
        let (nestedScript, nestedTacticState) ←
          tacticState.onGoalM goal.goal λ tacticState => go steps tacticState
        nestedScripts := nestedScripts.push (goalPos, nestedScript)
        tacticState := nestedTacticState
      let script := nestedScripts.foldr (init := .empty)
        λ (goalPos, nestedScript) tail =>
          .focusAndSolve goalPos nestedScript tail
      return (script, tacticState)

def matchGoals (postState₁ postState₂ : Meta.SavedState)
    (goals₁ goals₂ : Array MVarId) : MetaM (Option (HashMap MVarId MVarId)) := do
  let goals₁ ← getProperGoals postState₁ goals₁
  let goals₂ ← getProperGoals postState₂ goals₂
  let (equal, s) ←
    tacticStatesEqualUpToIds' none postState₁.meta.mctx
      postState₂.meta.mctx goals₁ goals₂ (allowAssignmentDiff := true)
        (ignoreFVar := λ ldecl => isForwardImplDetailHypName ldecl.userName)
      -- HACK ignoreFVar excludes the _fwd hypotheses added by forward rules.
      -- These are supposed to be `implDetail` hypotheses, which are ignored,
      -- but tactics using the revert/intro pattern, such as `subst`, can remove
      -- the `implDetail` attribute from these hypotheses.
  if ! equal then
    return none
  else
    return s.equalMVarIds
where
  getProperGoals (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM (Array MVarId) :=
    state.runMetaM' do
      let (properGoals, _) ← partitionGoalsAndMVars goals
      return properGoals.map (·.fst)

namespace DynStructureM

structure Context where
  /-- The tactic invocation steps corresponding to the original unstructured
  script, but with `MVarId` keys adjusted to fit the current `MetaM` state. This
  state evolves during dynamic structuring and we continually update the `steps`
  so that this map's keys refer to metavariables which exist in the current
  `MetaM` state. -/
  steps : PHashMap MVarId (Nat × TacticInvocation)
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

def DynStructureM.run (x : DynStructureM α) (script : UnstructuredScript) :
    MetaM α := do
  let mut steps : PHashMap MVarId (Nat × TacticInvocation) := {}
  for h : i in [:script.size] do
    let step := script[i]'h.2
    steps := steps.insert step.preGoal (i, step)
  ReaderT.run x { steps }

def withUpdatedMVarIds [MonadWithReader DynStructureM.Context m]
    [MonadLiftT MetaM m]
    (oldPostState newPostState : Meta.SavedState)
    (oldPostGoals newPostGoals : Array MVarId) (onFailure : m α)
    (onSuccess : m α) : m α := do
  match ← matchGoals newPostState oldPostState newPostGoals oldPostGoals with
  | some m => withReader (·.updateMVarIds m) onSuccess
  | none => onFailure

-- TODO upstream
local instance [Nonempty α] [Nonempty β] : Nonempty (α × β) :=
  ⟨Classical.ofNonempty, Classical.ofNonempty⟩

structure DynStructureResult where
  script : StructuredScript
  postState : Meta.SavedState
  postGoals : Array MVarId

partial def UnstructuredScript.toStructuredScriptDynamic
    (preState : Meta.SavedState) (preGoal : MVarId)
    (script : UnstructuredScript) : MetaM (Option StructuredScript) :=
  withAesopTraceNode .debug (λ r => return m!"{ExceptToEmoji.toEmoji r} structuring generated tactic script") do
    aesop_trace[debug] "unstructured script:{indentD $ toMessageData $ tacticsToTacticSeq $ script.concatMap (·.tacticSeq)}"
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
          let (some (_, ti)) := (← read).steps[preGoal]
            | throwError "found no step for goal {preGoal.name}:{indentD $ ← preState.runMetaM' do addMessageContext $ toMessageData preGoal}"
          aesop_trace[debug] "running tactics:{indentD $ toMessageData $ tacticsToTacticSeq ti.tacticSeq}"
          withConstAesopTraceNode .debug (return m!"expected post goals:") do
            aesop_trace[debug] ← goalsToMessageData ti.postState $ ti.postGoals.map (·.goal)
          let (postState, postGoals) ←
            try
              runTacticsCapturingPostState ti.tacticSeq preState preGoals.toList
            catch e =>
              aesop_trace[debug] "tactics failed with error:{indentD e.toMessageData}"
              return none
          let postGoals := postGoals.toArray
          withUpdatedMVarIds ti.postState postState
              (ti.postGoals.map (·.goal)) postGoals
              (onFailure := do
                aesop_trace[debug] "post goals don't match; actual post goals:{indentD $ ← goalsToMessageData postState postGoals}"
                return none) do
            aesop_trace[debug] "post goals match"
            let some { script := tailScript, postState, postGoals } ←
              goStructured postState postGoals
              | return none
            let script := .onGoal 0 ti tailScript
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
      let some (goalPos, goal, _, ti) := firstStep?
        | throwError "found no step for any of the visible goals{indentD $ ← goalsToMessageData preState preGoals}"
      aesop_trace[debug] "running tactics on goal {goalPos}:{indentD $ toMessageData $ tacticsToTacticSeq ti.tacticSeq}"
      withConstAesopTraceNode .debug (return m!"expected post goals:") do
        aesop_trace[debug] ← goalsToMessageData ti.postState $ ti.postGoals.map (·.goal)
      let (postState, postGoals) ←
        try
          runTacticsCapturingPostState ti.tacticSeq preState [goal]
        catch e =>
          aesop_trace[debug] "tactics failed with error:{indentD e.toMessageData}"
          return none
      let postGoals := postGoals.toArray
      withUpdatedMVarIds ti.postState postState
          (ti.postGoals.map (·.goal)) postGoals
          (onFailure := do
            aesop_trace[debug] "post goals don't match; actual post goals:{indentD $ ← goalsToMessageData postState postGoals}"
            return none) do
        aesop_trace[debug] "post goals match"
        let postGoals := preGoals[:goalPos] ++ postGoals ++ preGoals[goalPos+1:]
        let some { script := tailScript, postState, postGoals } ←
          go postState postGoals
          | return none
        let script := .onGoal goalPos ti tailScript
        return some { script, postState, postGoals }

  goalsToMessageData (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $
        MessageData.joinSep
          (goals.map λ g => m!"?{g.name}:{indentD $ toMessageData g}").toList
          "\n"

  tacticsToTacticSeq (ts : Array Syntax.Tactic) :
      TSyntax ``Lean.Parser.Tactic.tacticSeq :=
    Unhygienic.run do `(Lean.Parser.Tactic.tacticSeq| $ts:tactic*)

end Aesop
