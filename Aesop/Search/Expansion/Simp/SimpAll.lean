/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean
open Lean.Meta
open Std (HashMap)

namespace Aesop

-- Largely copy pasta, originally from Lean/Meta/Simp/SimpAll.lean.

private structure Entry where
  fvarId : FVarId -- original fvarId
  userName : Name
  id : Name   -- id of the theorem at `SimpTheorems`
  type : Expr
  proof : Expr
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
  disabledTheorems : HashMap FVarId Name
    -- If `fvarId` is mapped to `id` in this map, the simp theorem with name
    -- `id` is disabled while simplifying the hypothesis `fvarId`.
    --
    -- This should really be `HashMap FVarId (Array Name)`, but for the purposes
    -- of Aesop we only need a single disabled entry per FVarId.

private abbrev M := StateRefT State MetaM

private def initEntries : M Unit := do
  let hs ← withMVarContext (← get).mvarId do getPropHyps
  let hsNonDeps ← getNondepPropHyps (← get).mvarId
  let mut simpThms := (← get).ctx.simpTheorems
  for h in hs do
    let localDecl ← getLocalDecl h
    unless simpThms.isErased localDecl.userName do
      let fvarId := localDecl.fvarId
      let proof  := localDecl.toExpr
      let id     ← mkFreshUserName `h
      simpThms ← simpThms.addTheorem proof (name? := id)
      modify fun s => { s with ctx.simpTheorems := simpThms }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let entry : Entry := { fvarId := fvarId, userName := localDecl.userName, id := id, type := (← instantiateMVars localDecl.type), proof := proof }
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
    match (← simpStep (← get).mvarId entry.proof entry.type ctx) with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- The theorem for the simplified entry must use the same `id` of the theorem before simplification. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`. If we don't use the same `id`, in the next round
           the first version would simplify it to `h : True`.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        let simpThmsNew ← (← getSimpTheorems).addTheorem (← mkExpectedTypeHint proofNew typeNew) (name? := entry.id)
        modify fun s => { s with
          modified         := true
          anyModified      := true
          ctx.simpTheorems := simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := entry.id }
        }
  -- simplify target
  let mvarId := (← get).mvarId
  match (← simpTarget mvarId (← get).ctx) with
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
    return .solved
  else if ! (← get).anyModified then
    return .unchanged (← get).mvarId
  else
    let mvarId := (← get).mvarId
    let entries := (← get).entries
    let (_, mvarId) ← assertHypotheses mvarId (entries.map fun e => { userName := e.userName, type := e.type, value := e.proof })
    let mvarId ← tryClearMany mvarId (entries.map fun e => e.fvarId)
    return .simplified mvarId

def simpAll (mvarId : MVarId) (ctx : Simp.Context)
    (disabledTheorems : HashMap FVarId Name) : MetaM SimpResult := do
  withMVarContext mvarId do
    main.run' { mvarId, ctx, disabledTheorems }

end Aesop
