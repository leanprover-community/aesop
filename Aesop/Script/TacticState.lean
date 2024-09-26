/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Lean.Meta.Basic
import Aesop.Script.GoalWithMVars

open Lean

namespace Aesop.Script

variable [Monad m] [MonadError m]

structure TacticState where
  visibleGoals : Array GoalWithMVars
  invisibleGoals : Std.HashSet MVarId
  deriving Inhabited

namespace TacticState

def mkInitial (goal : MVarId) : MetaM TacticState :=
  return {
    visibleGoals := #[⟨goal, ← goal.getMVarDependencies⟩]
    invisibleGoals := ∅
  }

private def throwUnknownGoalError (goal : MVarId) (pre : MessageData) : m α :=
  throwError "internal error: {pre}: unknown goal '?{goal.name}'"

def getVisibleGoalIndex? (ts : TacticState) (goal : MVarId) : Option Nat :=
  ts.visibleGoals.findIdx? (·.goal == goal)

def getVisibleGoalIndex (ts : TacticState) (goal : MVarId) : m Nat := do
  if let (some idx) := ts.getVisibleGoalIndex? goal then
    return idx
  else
    throwUnknownGoalError goal "getVisibleGoalIndex"

def getMainGoal? (ts : TacticState) : Option MVarId :=
  ts.visibleGoals[0]?.map (·.goal)

def visibleGoalsHaveMVars (ts : TacticState) : Bool :=
  ts.visibleGoals.any λ g => ! g.mvars.isEmpty

def solveVisibleGoals (ts : TacticState) : TacticState :=
  { ts with visibleGoals := #[] }

private def replaceWithArray [BEq α] (xs : Array α) (x : α) (r : Array α) :
    Option (Array α) := Id.run do
  let mut found := false
  let mut ys := Array.mkEmpty (xs.size - 1 + r.size)
  for x' in xs do
    if x' == x then
      ys := ys ++ r
      found := true
    else
      ys := ys.push x'
  return if found then some ys else none

def eraseSolvedGoals (ts : TacticState) (preMCtx postMCtx : MetavarContext) :
    TacticState := {
  ts with
  visibleGoals := ts.visibleGoals.filter (! mvarWasSolved ·.goal)
  invisibleGoals := ts.invisibleGoals.filter (! mvarWasSolved ·)
}
where
  mvarWasSolved (mvarId : MVarId) : Bool :=
    postMCtx.isExprMVarAssignedOrDelayedAssigned mvarId &&
    ! preMCtx.isExprMVarAssignedOrDelayedAssigned mvarId

def applyTactic (ts : TacticState) (inGoal : MVarId)
    (outGoals : Array GoalWithMVars) (preMCtx postMCtx : MetavarContext) :
    m TacticState := do
  let (some visibleGoals) :=
        replaceWithArray ts.visibleGoals ⟨inGoal, {}⟩ outGoals
    | throwUnknownGoalError inGoal "applyTactic"
  let ts := { ts with visibleGoals }
  return eraseSolvedGoals ts preMCtx postMCtx

-- Focus the visible goal `goal` and move all other previously visible goals
-- to `invisibleGoals`.
def focus (ts : TacticState) (goal : MVarId) : m TacticState := do
  let (some goalWithMVars) := ts.visibleGoals.find? (·.goal == goal)
    | throwUnknownGoalError goal "focus"
  let mut invisibleGoals := ts.invisibleGoals
  for g in ts.visibleGoals do
    if g.goal != goal then
      invisibleGoals := invisibleGoals.insert g.goal
  return { visibleGoals := #[goalWithMVars], invisibleGoals }

@[inline, always_inline]
def onGoalM (ts : TacticState) (g : MVarId)
    (f : TacticState → m (α × TacticState)) : m (α × TacticState) := do
  let (a, postTs) ← f (← ts.focus g)
  let mut visibleGoals := #[]
  for preGoal in ts.visibleGoals do
    if preGoal.goal == g then
      visibleGoals := visibleGoals ++ postTs.visibleGoals
    else if postTs.invisibleGoals.contains preGoal.goal then
      visibleGoals := visibleGoals.push preGoal
  let mut invisibleGoals := ∅
  for g in ts.invisibleGoals do
    if postTs.invisibleGoals.contains g then
      invisibleGoals := invisibleGoals.insert g
  return (a, { visibleGoals, invisibleGoals })

end Aesop.Script.TacticState
