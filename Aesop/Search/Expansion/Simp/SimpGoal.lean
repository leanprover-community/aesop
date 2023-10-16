/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean Lean.Meta
open Lean.Meta.Simp (UsedSimps)

namespace Aesop

-- Largely copy pasta, originally from Lean/Meta/Simp/Main.lean.
-- TODO: Once https://github.com/leanprover/lean4/issues/2486 is fixed, we can
-- simply wrap core's simpGoal.

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM SimpResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mvarIdOld := mvarId
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut usedSimps := usedSimps
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
      let (r, usedSimps') ← simp type ctx discharge? usedSimps
      usedSimps := usedSimps'
      match r.proof? with
      | some _ =>
        match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return .solved usedSimps
        | some (value, type) =>
          toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.consumeMData.isConstOf ``False then
          mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
          return .solved usedSimps
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let (r, usedSimps') ← simpTarget mvarId ctx discharge? (usedSimps := usedSimps)
      usedSimps := usedSimps'
      match r with
      | none => return .solved usedSimps
      | some mvarIdNew =>
        mvarId := mvarIdNew
    let (_, mvarIdNew) ← mvarId.assertHypotheses toAssert
    mvarId := mvarIdNew
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    let mvarIdNew ← mvarIdNew.tryClearMany toClear
    if mvarId == mvarIdOld then
      return .unchanged mvarId
    else
      return .simplified mvarIdNew usedSimps

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
