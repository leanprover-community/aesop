/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean
open Lean.Meta

namespace Aesop

-- Copy pasta, originally from Lean/Meta/Simp/Main.lean.

def simpMainWithCache (e : Expr) (ctx : Simp.Context) (cache : Simp.Cache)
    (methods : Simp.Methods := {}) : MetaM (Simp.Result × Simp.Cache) := do
  let ctx := { ctx with config := (← ctx.config.updateArith) }
  withConfig (fun c => { c with etaStruct := ctx.config.etaStruct }) <| withReducible do
    try
      let (result, state) ← Simp.simp e methods ctx |>.run { cache := cache}
      return (result, state.cache)
    catch ex =>
      if ex.isMaxHeartbeat then throwNestedTacticEx `simp ex else throw ex

def simpWithCache (e : Expr) (ctx : Simp.Context) (cache : Simp.Cache)
    (discharge? : Option Simp.Discharge := none) :
    MetaM (Simp.Result × Simp.Cache) := do
  profileitM Exception "simp" (← getOptions) do
    match discharge? with
    | none   =>
      simpMainWithCache e ctx cache (methods := Simp.DefaultMethods.methods)
    | some d =>
      simpMainWithCache e ctx cache
        (methods := {
          pre := (Simp.preDefault · d)
          post := (Simp.postDefault · d)
          discharge? := d
        })

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetWithCacheCore (mvarId : MVarId) (ctx : Simp.Context)
    (cache : Simp.Cache) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) : MetaM (Option MVarId × Simp.Cache) := do
  let target ← instantiateMVars (← getMVarType mvarId)
  let (r, cache) ← simpWithCache target ctx cache discharge?
  if mayCloseGoal && r.expr.isConstOf ``True then
    match r.proof? with
    | some proof => assignExprMVar mvarId  (← mkOfEqTrue proof)
    | none => assignExprMVar mvarId (mkConst ``True.intro)
    return (none, cache)
  else
    let r ← applySimpResultToTarget mvarId target r
    return (r, cache)

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTargetWithCache (mvarId : MVarId) (ctx : Simp.Context)
    (cache : Simp.Cache) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) : MetaM (Option MVarId × Simp.Cache) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    simpTargetWithCacheCore mvarId ctx cache discharge? mayCloseGoal

def simpGoalWithCache (mvarId : MVarId) (ctx : Simp.Context)
    (cache : Simp.Cache) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (fvarIdToLemmaId : FVarIdToLemmaId := {}) :
    MetaM (Option (Array FVarId × MVarId) × Simp.Cache) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut cache := cache
    for fvarId in fvarIdsToSimp do
      let localDecl ← getLocalDecl fvarId
      let type ← instantiateMVars localDecl.type
      let (r, cache') ←
        match fvarIdToLemmaId.find? localDecl.fvarId with
        | none =>
          simpWithCache type ctx cache discharge?
        | some thmId =>
          let ctx :=
            { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem thmId }
          let r ← simp type ctx discharge?
          pure (r, cache)
      cache := cache'
      match r.proof? with
      | some proof => match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return (none, cache)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isConstOf ``False then
          assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) (mkFVar fvarId))
          return (none, cache)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← replaceLocalDeclDefEq mvarId fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let (targetSimpResult?, cache') ←
        simpTargetWithCache mvarId ctx cache discharge?
      cache := cache'
      match targetSimpResult? with
      | none => return (none, cache)
      | some mvarIdNew => mvarId := mvarIdNew
    let (fvarIdsNew, mvarIdNew) ← assertHypotheses mvarId toAssert
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    let mvarIdNew ← tryClearMany mvarIdNew toClear
    return (some (fvarIdsNew, mvarIdNew), cache)

end Aesop
