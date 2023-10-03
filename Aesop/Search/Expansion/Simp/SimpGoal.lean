/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean Lean.Meta
open Lean.Meta.Simp (UsedSimps)

namespace Aesop

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM SimpResult := do
  let mvarIdOld := mvarId
  let ctx := { ctx with config.failIfUnchanged := false }
  let (result, usedSimps) ←
    Meta.simpGoal mvarId ctx discharge? simplifyTarget fvarIdsToSimp usedSimps
  if let some (_, mvarId) := result then
    if mvarId == mvarIdOld then
      return .unchanged mvarId
    else
      return .simplified mvarId usedSimps
  else
    return .solved usedSimps

def simpGoalWithAllHypotheses (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (usedSimps : UsedSimps := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    let lctx ← getLCtx
    let mut fvarIdsToSimp := Array.mkEmpty lctx.decls.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      fvarIdsToSimp := fvarIdsToSimp.push ldecl.fvarId
    Aesop.simpGoal mvarId ctx discharge? simplifyTarget fvarIdsToSimp usedSimps

end Aesop
