/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean
open Lean.Meta
open Lean.Meta.Simp (UsedSimps)

namespace Aesop

-- Largely copy pasta, originally from Lean/Meta/Simp/SimpAll.lean.

private structure Entry where
  fvarId   : FVarId -- original fvarId
  userName : Name
  id       : Origin -- id of the theorem at `SimpTheorems`
  type     : Expr
  proof    : Expr
  deriving Inhabited

private structure State where
  modified : Bool := false
  anyModified : Bool := false
    -- Indicates whether any hypothesis or the target was modified. This is
    -- different from `modified` since `modified` is reset on every iteration of
    -- the main loop.
  mvarId  : MVarId
  entries : Array Entry := #[]
  ctx : Simp.Context
  usedSimps : UsedSimps := {}
  disabledTheorems : HashMap FVarId Origin
    -- If `fvarId` is mapped to `origin` in this map, the simp theorem `origin`
    -- is disabled while simplifying the hypothesis `fvarId`.
    --
    -- This should really be `HashMap FVarId (Array Origin)`, but for the
    -- purposes of Aesop we only need a single disabled entry per FVarId.

private abbrev M := StateRefT State MetaM

private def initEntries : M Unit := do
  let hs ←  (← get).mvarId.withContext do getPropHyps
  let hsNonDeps ← (← get).mvarId.getNondepPropHyps
  let mut simpThms := (← get).ctx.simpTheorems
  for h in hs do
    unless simpThms.isErased (.fvar h) do
      let localDecl ← h.getDecl
      let proof  := localDecl.toExpr
      simpThms ← simpThms.addTheorem (.fvar h) proof
      modify fun s => { s with ctx.simpTheorems := simpThms }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let entry : Entry := { fvarId := h, userName := localDecl.userName, id := .fvar h, type := (← instantiateMVars localDecl.type), proof := proof }
        modify fun s => { s with entries := s.entries.push entry }

private abbrev getSimpTheorems : M SimpTheoremsArray :=
  return (← get).ctx.simpTheorems

private partial def loop : M Bool := do
  modify fun s => { s with modified := false }
  -- simplify entries
  let entries := (← get).entries
  for h : i in [:entries.size] do
    let h : i < entries.size := by simp_all [Membership.mem]
    let entry := entries[i]
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let mut simpThmsWithoutEntry := (← getSimpTheorems).eraseTheorem entry.id
    -- Ditto for explicitly disabled entries.
    if let (some disabledEntry) := (← get).disabledTheorems.find? entry.fvarId then
      simpThmsWithoutEntry := simpThmsWithoutEntry.eraseTheorem disabledEntry
    let ctx := { ctx with simpTheorems := simpThmsWithoutEntry }
    let (r, usedSimps) ← simpStep (← get).mvarId entry.proof entry.type ctx (usedSimps := (← get).usedSimps)
    modify fun s => { s with usedSimps }
    match r with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- We must erase the `id` for the simplified theorem. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`.

           It is also important for avoiding identical hypotheses to simplify each other to `True`.
           Example
           ```
           ...
           h₁ : p a
           h₂ : p a
           ⊢ q a
           ```
           `h₁` is first simplified to `True`. If we don't remove `h₁` from the set of simp theorems, it will
           be used to simplify `h₂` to `True` and information is lost.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        trace[Meta.Tactic.simp.all] "entry.id: {← ppOrigin entry.id}, {entry.type} => {typeNew}"
        let mut simpThmsNew := (← getSimpTheorems).eraseTheorem (.fvar entry.fvarId)
        let idNew ← mkFreshId
        simpThmsNew ← simpThmsNew.addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew)
        modify fun s => { s with
          modified         := true
          anyModified      := true
          ctx.simpTheorems := simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := .other idNew }
        }
  -- simplify target
  let mvarId := (← get).mvarId
  let (r, usedSimps) ← simpTarget mvarId (← get).ctx (usedSimps := (← get).usedSimps)
  modify fun s => { s with usedSimps }
  match r with
  | none => return true
  | some mvarIdNew =>
    unless mvarId == mvarIdNew do
      modify fun s => { s with
        modified := true
        anyModified := true
        mvarId   := mvarIdNew
      }
  if (← get).modified then
    loop
  else
    return false

private def main : M SimpResult := do
  initEntries
  if (← loop) then
    return .solved (← get).usedSimps
  else if ! (← get).anyModified then
    return .unchanged (← get).mvarId
  else
    let mvarId := (← get).mvarId
    let entries := (← get).entries
    let (_, mvarId) ← mvarId.assertHypotheses <| entries.filterMap fun e =>
      -- Do not assert `True` hypotheses
      if e.type.isConstOf ``True then none else some { userName := e.userName, type := e.type, value := e.proof }
    let mvarId ← mvarId.tryClearMany (entries.map fun e => e.fvarId)
    return .simplified mvarId (← get).usedSimps

def simpAll (mvarId : MVarId) (ctx : Simp.Context)
    (disabledTheorems : HashMap FVarId Origin) (usedSimps : UsedSimps := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp_all
    (·.fst) <$> main.run { mvarId, ctx, usedSimps, disabledTheorems }

end Aesop
