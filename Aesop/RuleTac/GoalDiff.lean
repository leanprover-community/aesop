/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.BaseM
import Aesop.RuleTac.FVarIdSubst
import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

/--
A representation of the differences between two goals. Each Aesop rule produces
a `GoalDiff` between the goal on which the rule was run (the 'old goal') and
each of the subgoals produced by the rule (the 'new goals').

We use the produced `GoalDiff`s to update stateful data structures which cache
information about Aesop goals and for which it is more efficient to update the
cached information than to recompute it for each goal.

Hypotheses are identified by their `FVarId` *and* the RPINF of their type and
value (if any). This means that when a hypothesis `h : T` with `FVarId` `i`
appears in the old goal and `h : T'` with `FVarId` `i` appears in the new goal,
but the RPINF of `T` is not equal to the RPINF of `T'`, then `h` is treated as
both added (with the new type) and removed (with the old type). This can happen
when the type of a hyp changes to another type that is definitionally equal at
`default`, but not at `reducible` transparency.

The target is identified by RPINF.
-/
-- TODO Lean theoretically has an invariant that the type of an fvar cannot
-- change without the `FVarId` also changing. However, this invariant is
-- currently sometimes violated, notably by `simp`:
--
--   https://github.com/leanprover/lean4/issues/6226
--
-- If we could rely on this invariant, we could greatly simplify the computation
-- of goal diffs because we could trust that if an fvar is present in the old
-- and new goal, it has the same type in both.
structure GoalDiff where
  /-- The old goal. -/
  oldGoal : MVarId
  /-- The new goal. -/
  newGoal : MVarId
  /-- `FVarId`s that appear in the new goal, but not (or with a different type)
  in the old goal. -/
  addedFVars : Std.HashSet FVarId
  /-- `FVarId`s that appear in the old goal, but not (or with a different type)
  in the new goal. -/
  removedFVars : Std.HashSet FVarId
  /-- Is the old goal's target RPINF equal to the new goal's target RPINF? -/
  targetChanged : LBool
  deriving Inhabited

protected def GoalDiff.empty (oldGoal newGoal : MVarId) : GoalDiff := {
  addedFVars := ∅
  removedFVars := ∅
  targetChanged := .undef
  oldGoal, newGoal
}

def isRPINFEqual (goal₁ goal₂ : MVarId) (e₁ e₂ : Expr) : BaseM Bool :=
  return (← goal₁.withContext $ rpinf e₁) == (← goal₂.withContext $ rpinf e₂)

def isRPINFEqualLDecl (goal₁ goal₂ : MVarId) :
    (ldecl₁ ldecl₂ : LocalDecl) → BaseM Bool
  | .cdecl (type := type₁) .., .cdecl (type := type₂) .. =>
    isRPINFEqual goal₁ goal₂ type₁ type₂
  | .ldecl (type := type₁) (value := value₁) .., .ldecl (type := type₂) (value := value₂) .. =>
    isRPINFEqual goal₁ goal₂ type₁ type₂ <&&>
    isRPINFEqual goal₁ goal₂ value₁ value₂
  | _, _ => return false

def getNewFVars (oldGoal newGoal : MVarId) (oldLCtx newLCtx : LocalContext) :
    BaseM (Std.HashSet FVarId) :=
  newLCtx.foldlM (init := ∅) λ newFVars ldecl => do
    if ldecl.isImplementationDetail then
      return newFVars
    if let some oldLDecl := oldLCtx.find? ldecl.fvarId then
      if ← isRPINFEqualLDecl oldGoal newGoal oldLDecl ldecl then
        return newFVars
      else
        return newFVars.insert ldecl.fvarId
    else
      return newFVars.insert ldecl.fvarId

/--
Diff two goals.
-/
def diffGoals (old new : MVarId) : BaseM GoalDiff := do
  let oldLCtx := (← old.getDecl).lctx
  let newLCtx := (← new.getDecl).lctx
  return {
    oldGoal := old
    newGoal := new
    addedFVars := ← getNewFVars old new oldLCtx newLCtx
    removedFVars := ← getNewFVars new old newLCtx oldLCtx
    targetChanged :=
      ! (← isRPINFEqual old new (← old.getType) (← new.getType)) |>.toLBool
  }

namespace GoalDiff

def targetChanged' (diff : GoalDiff) : BaseM Bool :=
  match diff.targetChanged with
  | .true => return true
  | .false => return false
  | .undef => do
    let eq ←
      isRPINFEqual diff.oldGoal diff.newGoal (← diff.oldGoal.getType)
        (← diff.newGoal.getType)
    return ! eq

/--
If `diff₁` is the difference between goals `g₁` and `g₂` and `diff₂` is the
difference between `g₂` and `g₃`, then `diff₁.comp diff₂` is the difference
between `g₁` and `g₃`.

We assume that a hypothesis whose RPINF changed between `g₁` and `g₂` does not
change back, i.e. the hypothesis' RPINF is still different between `g₁` and `g₃`.
-/
def comp (diff₁ diff₂ : GoalDiff) : GoalDiff where
  oldGoal := diff₁.oldGoal
  newGoal := diff₂.newGoal
  addedFVars :=
    diff₁.addedFVars.fold (init := diff₂.addedFVars) λ addedFVars fvarId =>
      if diff₂.removedFVars.contains fvarId then
        addedFVars
      else
        addedFVars.insert fvarId
  removedFVars :=
    diff₂.removedFVars.fold (init := diff₁.removedFVars) λ removedFVars fvarId =>
      if diff₁.addedFVars.contains fvarId then
        removedFVars
      else
        removedFVars.insert fvarId
  targetChanged := lBoolOr diff₁.targetChanged diff₂.targetChanged

def checkCore (diff : GoalDiff) (old new : MVarId) :
    BaseM (Option MessageData) := do
  if diff.oldGoal != old then
    return some m!"incorrect old goal: expected {old.name}, got {diff.oldGoal.name}"
  if diff.newGoal != new then
    return some m!"incorrect new goal: expected {new.name}, got {diff.newGoal.name}"

  let oldLCtx := (← old.getDecl).lctx
  let newLCtx := (← new.getDecl).lctx

  -- Check that the added hypotheses were indeed added
  for fvarId in diff.addedFVars do
    if let some oldLDecl := oldLCtx.find? fvarId then
      if ← isRPINFEqualLDecl old new oldLDecl (← fvarId.getDecl) then
        return some m!"addedFVars contains hypothesis {oldLDecl.userName} which was already present in the old goal"
    unless newLCtx.contains fvarId do
      return some m!"addedFVars contains hypothesis {fvarId.name} but this fvar does not exist in the new goal"

  -- Check that the removed hypotheses were indeed removed
  for fvarId in diff.removedFVars do
    if let some newLDecl := newLCtx.find? fvarId then
      if ← isRPINFEqualLDecl old new (← fvarId.getDecl) newLDecl then
        return some m!"removedFVars contains hypothesis {newLDecl.userName} but it is still present in the new goal"
    unless oldLCtx.contains fvarId do
      return some m!"removedFVars contains hypothesis {fvarId.name} but this fvar does not exist in the old goal"

  -- Check that all added hypotheses appear in addedFVars
  for newLDecl in newLCtx do
    if newLDecl.isImplementationDetail then
      continue
    let newFVarId := newLDecl.fvarId
    if ! oldLCtx.contains newFVarId &&
       ! diff.addedFVars.contains newFVarId then
      return some m!"hypothesis {newLDecl.userName} was added, but does not appear in addedFVars"

  -- Check that all removed hypotheses appear in removedFVars
  for oldLDecl in oldLCtx do
    if oldLDecl.isImplementationDetail then
      continue
    let oldFVarId := oldLDecl.fvarId
    if ! newLCtx.contains oldFVarId &&
       ! diff.removedFVars.contains oldFVarId then
      return some m!"hypothesis {oldLDecl.userName} was removed, but does not appear in removedFVars"

  -- Check that all common hypotheses have equal RPINFs
  for newLDecl in newLCtx do
    if newLDecl.isImplementationDetail then
      continue
    if let some oldLDecl := oldLCtx.find? newLDecl.fvarId then
      unless ← isRPINFEqualLDecl old new oldLDecl newLDecl do
        return some m!"hypotheses {oldLDecl.userName} and {newLDecl.userName} have the same FVarId but their types/values are not reducibly defeq"

  -- Check the target
  let oldTgt ← old.getType
  let newTgt ← new.getType
  if ← (pure $ diff.targetChanged == .true) <&&>
     isRPINFEqual old new oldTgt newTgt then
    let oldTgt ← old.withContext do addMessageContext m!"{oldTgt}"
    let newTgt ← new.withContext do addMessageContext m!"{newTgt}"
    return some m!"diff says target changed, but old target{indentD oldTgt}\nis reducibly defeq to new target{indentD newTgt}"
  if ← (pure $ diff.targetChanged == .false) <&&>
     notM (isRPINFEqual old new oldTgt newTgt) then
    let oldTgt ← old.withContext do addMessageContext m!"{oldTgt}"
    let newTgt ← new.withContext do addMessageContext m!"{newTgt}"
    return some m!"diff says target did not change, but old target{indentD oldTgt}\nis not reducibly defeq to new target{indentD newTgt}"

  return none

def check (diff : GoalDiff) (old new : MVarId) :
    BaseM (Option MessageData) := do
  if let some err ← diff.checkCore old new then
    addMessageContext m!"rule produced incorrect diff:{indentD err}\nold goal:{indentD old}\nnew goal:{indentD new}"
  else
    return none

end Aesop.GoalDiff
