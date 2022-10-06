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

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true)
    (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {})
    (disabledTheorems : HashMap FVarId Origin := {}) :
    MetaM (SimpResult × UsedSimps) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut usedSimps := usedSimps
    let mut progress := false
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
      let ctx :=
        match disabledTheorems.find? fvarId with
        | none => ctx
        | some thmId =>
          { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem thmId }
      let (r, usedSimps') ← simp type ctx discharge? usedSimps
      usedSimps := usedSimps'
      progress := progress || type != r.expr
      match r.proof? with
      | some _ =>
        match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return (.solved, usedSimps)
        | some (value, type) =>
          toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isConstOf ``False then
          mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
          return (.solved, usedSimps)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let preSimpTarget ← instantiateMVars (← mvarId.getType)
      let (r, usedSimps') ← simpTarget mvarId ctx discharge? (usedSimps := usedSimps)
      usedSimps := usedSimps'
      match r with
      | none => return (.solved, usedSimps)
      | some mvarIdNew =>
        let postSimpTarget ← instantiateMVars (← mvarIdNew.getType)
        progress := progress || preSimpTarget != postSimpTarget
        mvarId := mvarIdNew
    if ! progress then
      return (.unchanged mvarId, usedSimps)
    else
      let (_, mvarIdNew) ← mvarId.assertHypotheses toAssert
      let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
      let mvarIdNew ← mvarIdNew.tryClearMany toClear
      return (.simplified mvarIdNew, usedSimps)

end Aesop
