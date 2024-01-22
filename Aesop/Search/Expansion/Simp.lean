/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Script
import Aesop.RuleSet

open Lean Lean.Meta
open Simp (UsedSimps)

namespace Aesop

inductive SimpResult
  | solved (usedTheorems : Simp.UsedSimps)
  | unchanged (newGoal : MVarId)
  | simplified (newGoal : MVarId) (usedTheorems : UsedSimps)

namespace SimpResult

def newGoal? : SimpResult → Option MVarId
  | solved .. => none
  | unchanged g => some g
  | simplified g .. => some g

end SimpResult

variable [Monad m] [MonadQuotation m] [MonadError m]

def mkNormSimpSyntax (normSimpUseHyps : Bool)
    (configStx? : Option Term) : MetaM Syntax.Tactic := do
  if normSimpUseHyps then
    match configStx? with
    | none => `(tactic| simp_all)
    | some cfg => `(tactic| simp_all (config := $cfg))
  else
    match configStx? with
    | none => `(tactic| simp at *)
    | some cfg => `(tactic| simp (config := $cfg) at *)

def mkNormSimpOnlySyntax (inGoal : MVarId) (normSimpUseHyps : Bool)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    MetaM Syntax.Tactic := do
  let originalStx ← mkNormSimpSyntax normSimpUseHyps configStx?
  let stx ← inGoal.withContext do
    Elab.Tactic.mkSimpOnly originalStx usedTheorems
  return ⟨stx⟩

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : Simprocs)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM SimpResult := do
  let mvarIdOld := mvarId
  let ctx := { ctx with config.failIfUnchanged := false }
  let (result, usedSimps) ←
    Meta.simpGoal mvarId ctx simprocs discharge? simplifyTarget fvarIdsToSimp
      usedSimps
  if let some (_, mvarId) := result then
    if mvarId == mvarIdOld then
      return .unchanged mvarId
    else
      return .simplified mvarId usedSimps
  else
    return .solved usedSimps

def simpGoalWithAllHypotheses (mvarId : MVarId) (ctx : Simp.Context)
    (simprocs : Simprocs := {}) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (usedSimps : UsedSimps := {}) :
    MetaM SimpResult :=
  mvarId.withContext do
    let lctx ← getLCtx
    let mut fvarIdsToSimp := Array.mkEmpty lctx.decls.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      fvarIdsToSimp := fvarIdsToSimp.push ldecl.fvarId
    Aesop.simpGoal mvarId ctx simprocs discharge? simplifyTarget fvarIdsToSimp
      usedSimps

def simpAll (mvarId : MVarId) (ctx : Simp.Context) (simprocs : Simprocs := {})
    (usedSimps : UsedSimps := {}) : MetaM SimpResult := do
  let ctx := { ctx with config.failIfUnchanged := false }
  match ← Lean.Meta.simpAll mvarId ctx simprocs usedSimps with
  | (none, usedSimps) => return .solved usedSimps
  | (some mvarIdNew, usedSimps) =>
    if mvarIdNew == mvarId then
      return .unchanged mvarIdNew
    else
      return .simplified mvarIdNew usedSimps

end Aesop
