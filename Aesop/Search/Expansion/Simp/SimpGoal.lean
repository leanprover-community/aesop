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
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut progress := false
    for fvarId in fvarIdsToSimp do
      let ldecl ← getLocalDecl fvarId
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
          assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) (mkFVar fvarId))
          return .solved
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← replaceLocalDeclDefEq mvarId fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let preSimpTarget ← instantiateMVars (← getMVarType mvarId)
      match ← simpTarget mvarId ctx discharge? with
      | none => return .solved
      | some mvarIdNew =>
        let postSimpTarget ← instantiateMVars (← getMVarType mvarIdNew)
        progress := progress || preSimpTarget != postSimpTarget
    if ! progress then
      return .unchanged mvarId
    else
      let (_, mvarIdNew) ← assertHypotheses mvarId toAssert
      let toClear := fvarIdsToSimp.filter (! replaced.contains ·)
      let mvarIdNew ← tryClearMany mvarIdNew toClear
      return .simplified mvarIdNew

end Aesop
