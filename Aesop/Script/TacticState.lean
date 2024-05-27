/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.ScriptBuilder

open Lean

namespace Aesop

structure GoalWithMVars where
  goal : MVarId
  mvars : HashSet MVarId
  deriving Inhabited

instance : Repr GoalWithMVars where
  reprPrec
    | g, _ => s!"\{ goal := {repr g.goal}, mvars := {repr g.mvars.toArray} }"

instance : BEq GoalWithMVars :=
  ⟨λ g₁ g₂ => g₁.goal == g₂.goal⟩

def GoalWithMVars.ofMVarId (goal : MVarId) : MetaM GoalWithMVars := do
  return { goal, mvars := ← goal.getMVarDependencies }


variable [Monad m] [MonadError m]

structure TacticState where
  visibleGoals : Array GoalWithMVars
  invisibleGoals : HashSet MVarId
  deriving Inhabited

namespace TacticState

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

def hasNoVisibleGoals (ts : TacticState) : Bool :=
  ts.visibleGoals.isEmpty

def hasSingleVisibleGoal (ts : TacticState) : Bool :=
  ts.visibleGoals.size == 1

def visibleGoalsHaveMVars (ts : TacticState) : Bool :=
  ts.visibleGoals.any λ g => ! g.mvars.isEmpty

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

def eraseSolvedGoals (ts : TacticState) (mctx : MetavarContext) :
    TacticState := {
  ts with
  visibleGoals :=
    ts.visibleGoals.filter (! mctx.isExprMVarAssignedOrDelayedAssigned ·.goal)
  invisibleGoals :=
    HashSet.filter ts.invisibleGoals
      (! mctx.isExprMVarAssignedOrDelayedAssigned ·)
}

def applyTactic (ts : TacticState) (inGoal : MVarId)
    (outGoals : Array GoalWithMVars) (postMCtx : MetavarContext) :
    m TacticState := do
  let (some visibleGoals) :=
        replaceWithArray ts.visibleGoals ⟨inGoal, {}⟩ outGoals
    | throwUnknownGoalError inGoal "applyTactic"
  let ts := { ts with visibleGoals }
  return eraseSolvedGoals ts postMCtx

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
  return (a, { visibleGoals, invisibleGoals := postTs.invisibleGoals })

end Aesop.TacticState
