/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean Lean.Meta
open Std (HashMap)

namespace Aesop

-- Largely copy pasta, originally from Lean/Meta/Simp/Main.lean.

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true)
    (fvarIdsToSimp : Array FVarId := #[])
    (fvarIdToLemmaId : HashMap FVarId Name := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut progress := false
    for fvarId in fvarIdsToSimp do
      let ldecl ← fvarId.getDecl
      let type ← instantiateMVars ldecl.type
      let ctx :=
        match fvarIdToLemmaId.find? fvarId with
        | none => ctx
        | some thmId =>
          { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem thmId }
      let r ← simp type ctx discharge?
      progress := progress || type != r.expr
      match r.proof? with
      | some _ =>
        match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return .solved
        | some (value, type) =>
          toAssert := toAssert.push { userName := ldecl.userName, type := type, value := value }
      | none =>
        if r.expr.isConstOf ``False then
          mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
          return .solved
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let preSimpTarget ← instantiateMVars (← mvarId.getType)
      match ← simpTarget mvarId ctx discharge? with
      | none => return .solved
      | some mvarIdNew =>
        let postSimpTarget ← instantiateMVars (← mvarIdNew.getType)
        progress := progress || preSimpTarget != postSimpTarget
        mvarId := mvarIdNew
    if ! progress then
      return .unchanged mvarId
    else
      let (_, mvarIdNew) ← mvarId.assertHypotheses toAssert
      let toClear := fvarIdsToSimp.filter (! replaced.contains ·)
      let mvarIdNew ← mvarIdNew.tryClearMany toClear
      return .simplified mvarIdNew

end Aesop
