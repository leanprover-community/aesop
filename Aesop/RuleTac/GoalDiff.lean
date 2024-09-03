/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

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

For a goal diff between an old goal with local context `Γ` and a new goal with
local context `Δ`, we expect that

```text
Δ = (Γ \ removedFVars) ∪ addedFVars
```

when the local contexts are viewed as sets of `FVarId`s (excluding
implementation detail hypotheses).

As an optimisation, the goal diff additionally contains an `fvarSubst :
FVarIdSubst` which tracks renamings of hypotheses. When the substitution
contains a mapping `h ↦ h'`, this means that `h` was renamed to `h'`. Note that
we do not guarantee that for all such mappings, `h` actually appears in the old
goal and `h'` in the new goal. But if they do, `fvarSubst(T)` and `T'` must be
defeq in the context of the new goal, where `h : T`, `h' : T'` and
`fvarSubst(T)` is the application of the substitution to `T`. If `h` and `h'`
are `let` decls with values `v` and `v'`, `fvarSubst(v)` must additionally be
defeq to `v'`.

The `fvarSubst` is semantically irrelevant: it does not influence the sets of
added and removed hypotheses. However, it is an important performance
optimisation, so rules should strive to generate accurate substitutions whenever
possible.
-/
structure GoalDiff where
  /--
  `FVarId`s that appear in the new goal, but not in the old goal.
  -/
  addedFVars : Std.HashSet FVarId
  /--
  `FVarId`s that appear in the old goal, but not in the new goal.
  -/
  removedFVars : Std.HashSet FVarId
  /--
  An `FVarId` substitution that tracks hypotheses which have been renamed (but
  have not otherwise been modified).
  -/
  fvarSubst : FVarIdSubst
  deriving Inhabited

protected def GoalDiff.empty : GoalDiff where
  addedFVars := ∅
  removedFVars := ∅
  fvarSubst := ∅

instance : EmptyCollection GoalDiff :=
  ⟨.empty⟩

def getNewFVars (oldLCtx newLCtx : LocalContext) : Std.HashSet FVarId :=
  newLCtx.foldl (init := ∅) λ newFVars ldecl =>
    if ! ldecl.isImplementationDetail && ! oldLCtx.contains ldecl.fvarId then
      newFVars.insert ldecl.fvarId
    else
      newFVars

/--
Diff two goals.
-/
def diffGoals (old new : MVarId) (fvarSubst : FVarIdSubst) :
    MetaM GoalDiff := do
  let oldLCtx := (← old.getDecl).lctx
  let newLCtx := (← new.getDecl).lctx
  return {
    addedFVars := getNewFVars oldLCtx newLCtx
    removedFVars := getNewFVars newLCtx oldLCtx
    fvarSubst
  }

namespace GoalDiff

/--
If `diff₁` is the difference between goals `g₁` and `g₂` and `diff₂` is the
difference between `g₂` and `g₃`, then `diff₁.comp diff₂` is the difference
between `g₁` and `g₃`.
-/
def comp (diff₁ diff₂ : GoalDiff) : GoalDiff where
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
  fvarSubst := diff₁.fvarSubst.append diff₂.fvarSubst

def checkCore (diff : GoalDiff) (old new : MVarId) :
    MetaM (Option MessageData) := do
  let oldLCtx := (← old.getDecl).lctx
  let newLCtx := (← new.getDecl).lctx

  -- Check that the added hypotheses were indeed added
  for fvarId in diff.addedFVars do
    if let some ldecl := oldLCtx.find? fvarId then
      return some m!"addedFVars contains hypothesis {ldecl.userName} which was already present in the old goal"
    unless newLCtx.contains fvarId do
      return some m!"addedFVars contains hypothesis {fvarId.name} but this fvar does not exist in the new goal"

  -- Check that the removed hypotheses were indeed removed
  for fvarId in diff.removedFVars do
    if let some ldecl := newLCtx.find? fvarId then
      return some m!"removedFVars contains hypothesis {ldecl.userName} but it is still present in the new goal"
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

  -- Check that all common hypotheses are defeq
  for newLDecl in newLCtx do
    if newLDecl.isImplementationDetail then
      continue
    if let some oldLDecl := oldLCtx.find? newLDecl.fvarId then
      let equalLDecls ← new.withContext do
        isDefeqLocalDecl (diff.fvarSubst.applyToLocalDecl oldLDecl) newLDecl
      unless equalLDecls do
        return some m!"hypotheses {oldLDecl.userName} and {newLDecl.userName} have the same FvarId but are not defeq"

  -- Check the fvarSubst
  for (oldFVarId, newFVarId) in diff.fvarSubst.map do
    let some oldLDecl := oldLCtx.find? oldFVarId
      | continue
    if oldLDecl.isImplementationDetail then
      continue
    let some newLDecl := newLCtx.find? newFVarId
      | continue
    if newLDecl.isImplementationDetail then
      return some m!"fvarSubst maps hypothesis {oldLDecl.userName} to {newLDecl.userName}, but {newLDecl.userName} is an implementation detail"
    let equalLDecls ← new.withContext do
      isDefeqLocalDecl (diff.fvarSubst.applyToLocalDecl oldLDecl) newLDecl
    unless equalLDecls do
      return some m!"fvarSubst maps hypothesis {oldLDecl.userName} to {newLDecl.userName} but these hypotheses are not defeq"

  return none
where
  isDefeqLocalDecl : LocalDecl → LocalDecl → MetaM Bool
    | .cdecl (type := type₁) ..,
      .cdecl (type := type₂) .. =>
        isDefEq type₁ type₂
    | .ldecl (type := type₁) (value := value₁) ..,
      .ldecl (type := type₂) (value := value₂) .. =>
        isDefEq type₁ type₂ <&&> isDefEq value₁ value₂
    | _, _ => return false

def check (diff : GoalDiff) (old new : MVarId) :
    MetaM (Option MessageData) := do
  if let some err ← diff.checkCore old new then
    addMessageContext m!"rule produced incorrect diff:{indentD err}\nold goal:{indentD old}\nnew goal:{indentD new}"
  else
    return none

end Aesop.GoalDiff
