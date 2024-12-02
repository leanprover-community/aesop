/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Lean.Meta.Tactic.Simp.SimpAll

open Lean Lean.Meta
open Simp (UsedSimps)

namespace Aesop

inductive SimpResult
  | solved (usedTheorems : Simp.UsedSimps)
  | unchanged
  | simplified (newGoal : MVarId) (usedTheorems : UsedSimps)

namespace SimpResult

def newGoal? : SimpResult → Option MVarId
  | solved .. => none
  | unchanged => none
  | simplified g .. => some g

end SimpResult

/--
Add all `let` hypotheses in the local context as `simp` theorems.

Background: by default, in the goal `x : _ := v ⊢ P[x]`, `simp` does not
substitute `x` by `v` in the target. The `simp` option `zetaDelta` can be used
to make `simp` perform this substitution, but we don't want to set it because
then Aesop `simp` would diverge from default `simp`, so we would have to adjust
the `aesop?` output as well. Instead, we add `let` hypotheses explicitly. This
way, `simp?` picks them up as well.

See lean4#3520.
-/
def addLetDeclsToSimpTheorems (ctx : Simp.Context) : MetaM Simp.Context := do
  let mut simpTheoremsArray := ctx.simpTheorems
  if simpTheoremsArray.isEmpty then
    simpTheoremsArray := #[{}]
  for ldecl in ← getLCtx do
    if ldecl.hasValue && ! ldecl.isImplementationDetail then
      simpTheoremsArray := simpTheoremsArray.modify 0 λ simpTheorems =>
        simpTheorems.addLetDeclToUnfold ldecl.fvarId
  return ctx.setSimpTheorems simpTheoremsArray

def addLetDeclsToSimpTheoremsUnlessZetaDelta (ctx : Simp.Context) :
    MetaM Simp.Context := do
  if ctx.config.zetaDelta then
    return ctx
  else
    addLetDeclsToSimpTheorems ctx

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Simp.Stats := {}) : MetaM SimpResult := do
  let mvarIdOld := mvarId
  let ctx := ctx.setFailIfUnchanged false
  let (result, { usedTheorems := usedSimps, .. }) ←
    Meta.simpGoal mvarId ctx simprocs discharge? simplifyTarget fvarIdsToSimp
      stats
  if let some (_, mvarId) := result then
    if mvarId == mvarIdOld then
      return .unchanged
    else
      return .simplified mvarId usedSimps
  else
    return .solved usedSimps

def simpGoalWithAllHypotheses (mvarId : MVarId) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (stats : Simp.Stats := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    let lctx ← getLCtx
    let mut fvarIdsToSimp := Array.mkEmpty lctx.decls.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      fvarIdsToSimp := fvarIdsToSimp.push ldecl.fvarId
    let ctx ← addLetDeclsToSimpTheoremsUnlessZetaDelta ctx
    Aesop.simpGoal mvarId ctx simprocs discharge? simplifyTarget fvarIdsToSimp
      stats

def simpAll (mvarId : MVarId) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (stats : Simp.Stats := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    let ctx := ctx.setFailIfUnchanged false
    let ctx ← addLetDeclsToSimpTheoremsUnlessZetaDelta ctx
    match ← Lean.Meta.simpAll mvarId ctx simprocs stats with
    | (none, stats) => return .solved stats.usedTheorems
    | (some mvarIdNew, stats) =>
      if mvarIdNew == mvarId then
        return .unchanged
      else
        return .simplified mvarIdNew stats.usedTheorems

end Aesop
