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

-- Copy-pasta from Lean.Elab.Tactic.traceSimpCall.
-- `stx` is the syntax of the original `simp`/`simp_all`/`simp?`/`simp_all?`
-- call.
def mkSimpOnly (inGoal : MVarId) (stx : Syntax) (usedSimps : UsedSimps)
    (includeFVars : Bool) : MetaM Syntax :=
  inGoal.withContext do
    let mut stx := stx
    if stx[3].isNone then
      stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
    let mut args : Array Syntax := #[]
    let mut localsOrStar := some #[]
    let lctx ← getLCtx
    let env ← getEnv
    for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
      match thm with
      | .decl declName inv => -- global definitions in the environment
        if env.contains declName && !Lean.Elab.Tactic.simpOnlyBuiltins.contains declName then
          args := args.push (← if inv then
            `(Parser.Tactic.simpLemma| ← $(mkIdent (← unresolveNameGlobal declName)):ident)
          else
            `(Parser.Tactic.simpLemma| $(mkIdent (← unresolveNameGlobal declName)):ident))
      | .fvar fvarId => -- local hypotheses in the context
        if ! includeFVars then
          continue
        if let some ldecl := lctx.find? fvarId then
          localsOrStar := localsOrStar.bind fun locals =>
            if !ldecl.userName.isInaccessibleUserName &&
                (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
              some (locals.push ldecl.userName)
            else
              none
        -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
        -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
      | .stx _ thmStx => -- simp theorems provided in the local invocation
        args := args.push thmStx
      | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
        pure ()     -- We can't display them anyway.
    if let some locals := localsOrStar then
      args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
    else
      args := args.push (← `(Parser.Tactic.simpStar| *))
    let argsStx := if args.isEmpty then #[] else #[mkAtom "[", (mkAtom ",").mkSep args, mkAtom "]"]
    stx := stx.setArg 4 (mkNullNode argsStx)
    return stx

def mkNormSimpSyntax (useHyps : Bool) (configStx? : Option Term) :
    MetaM Syntax.Tactic := do
  if useHyps then
    match configStx? with
    | none => `(tactic| simp_all)
    | some cfg => `(tactic| simp_all (config := $cfg))
  else
    match configStx? with
    | none => `(tactic| simp at *)
    | some cfg => `(tactic| simp (config := $cfg) at *)

def mkNormSimpOnlySyntax (inGoal : MVarId) (useHyps : Bool)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    MetaM Syntax.Tactic := do
  let originalStx ← mkNormSimpSyntax useHyps configStx?
  let stx ←
    mkSimpOnly inGoal originalStx usedTheorems (includeFVars := ! useHyps)
  return ⟨stx⟩

def simpGoal (mvarId : MVarId) (ctx : Simp.Context)
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM (SimpResult × Array FVarId) := do
  let mvarIdOld := mvarId
  let ctx := { ctx with config.failIfUnchanged := false }
  let (result, usedSimps) ←
    Meta.simpGoal mvarId ctx discharge? simplifyTarget fvarIdsToSimp usedSimps
  if let some (newFVarIds, mvarId) := result then
    if mvarId == mvarIdOld then
      return (.unchanged mvarId, #[])
    else
      return (.simplified mvarId usedSimps, newFVarIds)
  else
    return (.solved usedSimps, #[])

def simpAtStar (mvarId : MVarId) (ctx : Simp.Context)
    (normalHypotheses : HashSet FVarId)
    (discharge? : Option Simp.Discharge := none) (simplifyTarget : Bool := true)
    (usedSimps : UsedSimps := {}) : MetaM (SimpResult × HashSet FVarId) := do
  let mut fvarIdsToSimp := Array.mkEmpty (← getLCtx).numIndices
  for fvarId in ← mvarId.getNondepPropHyps do
    if ! normalHypotheses.contains fvarId then
      fvarIdsToSimp := fvarIdsToSimp.push fvarId
  let (result, newFVarIds) ←
    Aesop.simpGoal mvarId ctx discharge? simplifyTarget fvarIdsToSimp usedSimps
  let normalHypotheses := normalHypotheses.insertMany newFVarIds
  return (result, normalHypotheses)

def simpAll (mvarId : MVarId) (ctx : Simp.Context)
    (usedSimps : UsedSimps := {}) : MetaM SimpResult := do
  let ctx := { ctx with config.failIfUnchanged := false }
  match ← Lean.Meta.simpAll mvarId ctx usedSimps with
  | (none, usedSimps) => return .solved usedSimps
  | (some mvarIdNew, usedSimps) =>
    if mvarIdNew == mvarId then
      return .unchanged mvarIdNew
    else
      return .simplified mvarIdNew usedSimps

end Aesop
