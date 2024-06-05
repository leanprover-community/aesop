/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.EqualUpToIds
import Aesop.Script.Tactic
import Aesop.Script.TacticState
import Batteries.Tactic.PermuteGoals

open Lean Lean.Meta

variable [Monad m] [MonadError m] [MonadQuotation m]

namespace Aesop.Script

@[inline]
def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1

def mkOnGoal (goalPos : Nat) (tac : Syntax.Tactic) : Syntax.Tactic :=
  if goalPos == 0 then
    tac
  else
    let posLit := mkOneBasedNumLit goalPos
    Unhygienic.run `(tactic| on_goal $posLit:num => $tac:tactic)

structure Step where
  preState : Meta.SavedState
  preGoal : MVarId
  tactic : Tactic
  postState : Meta.SavedState
  postGoals : Array GoalWithMVars

def TacticState.applyStep (tacticState : TacticState) (step : Step) :
    m TacticState :=
  tacticState.applyTactic step.preGoal step.postGoals step.preState.meta.mctx
    step.postState.meta.mctx

namespace Step

def uTactic (s : Step) : UTactic :=
  s.tactic.uTactic

def sTactic? (s : Step) : Option STactic :=
  s.tactic.sTactic?

instance : ToMessageData Step where
  toMessageData step :=
    m!"{step.preGoal.name} → {step.postGoals.map (·.goal.name)}:{indentD $ toMessageData step.tactic}"

def render (acc : Array Syntax.Tactic) (step : Step)
    (tacticState : TacticState) : m (Array Syntax.Tactic × TacticState) := do
  let pos ← tacticState.getVisibleGoalIndex step.preGoal
  let tacticState ← tacticState.applyStep step
  let acc := acc.push $ mkOnGoal pos step.tactic.uTactic
  return (acc, tacticState)

open Lean.Elab.Tactic (evalTactic) in
def validate (step : Step) : MetaM Unit := do
  let preMCtx := step.preState.meta.mctx
  let expectedPostMCtx := step.postState.meta.mctx
  let expectedPostGoals := step.postGoals |>.map (·.goal)
  let tac := step.uTactic
  let (actualPostState, actualPostGoals) ←
    try
      runTacticMCapturingPostState (evalTactic tac) step.preState [step.preGoal]
    catch e =>
      throwError "tactic{indentD step.uTactic}\nfailed with error{indentD e.toMessageData}"
  let actualPostGoals := actualPostGoals.toArray
  unless ← tacticStatesEqualUpToIds preMCtx expectedPostMCtx
      actualPostState.meta.mctx expectedPostGoals actualPostGoals do
    throwError "tactic{indentD tac}\nsucceeded but did not generate expected state. Initial goal:{indentD $ ← fmtGoals step.preState #[step.preGoal]}\nExpected goals:{indentD $ ← fmtGoals step.postState $ step.postGoals.map (·.goal)}\nActual goals:{indentD $ ← fmtGoals actualPostState actualPostGoals}"
where
  fmtGoals (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $
        MessageData.joinSep (← goals.mapM (λ g => return m!"{g}")).toList "\n"

end Step

structure LazyStep where
  preState : Meta.SavedState
  preGoal : MVarId
  tacticBuilder : TacticBuilder
  postState : Meta.SavedState
  postGoals : Array MVarId

namespace LazyStep

def toStep (s : LazyStep) : MetaM Step :=
  s.postState.runMetaM' do
    return {
      s with
      tactic := ← s.tacticBuilder
      postGoals := ← s.postGoals.mapM GoalWithMVars.ofMVarId
    }

structure BuildInput (α) where
  tac : MetaM α
  postGoals : α → Array MVarId
  tacticBuilder : α → TacticBuilder

@[inline, always_inline]
def build (preGoal : MVarId) (i : BuildInput α) : MetaM (LazyStep × α) := do
  let preState ← saveState
  let a ← i.tac
  let postState ← saveState
  let step := {
    tacticBuilder := i.tacticBuilder a
    postGoals := i.postGoals a
    preGoal, preState, postState
  }
  return (step, a)

def erasePostStateAssignments (s : LazyStep) (gs : Array MVarId) : LazyStep :=
  { s with
    postState.meta.mctx :=
      gs.foldl (init := s.postState.meta.mctx) λ mctx g =>
        mctx.eraseExprMVarAssignment g }

end Aesop.Script.LazyStep
