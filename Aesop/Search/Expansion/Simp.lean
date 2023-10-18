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

-- TODO copy-pasta from Lean.Elab.Tactic.traceSimpCall
-- NOTE: Must be executed in the context of the goal on which `simp` was run.
-- `stx` is the syntax of the original `simp`/`simp_all`/`simp?`/`simp_all?`
-- call.
def mkSimpOnly (stx : Syntax) (usedSimps : UsedSimps) (includeFVars : Bool) :
    MetaM Syntax := do
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

-- TODO this way to handle (config := ...) is ugly.
def mkNormSimpSyntax (normSimpUseHyps : Bool)
    (configStx? : Option Term) : MetaM Syntax.Tactic := do
  if normSimpUseHyps then
    match configStx? with
    | none => `(tactic| simp_all)
    | some cfg =>
      `(tactic| simp_all (config := ($cfg : Aesop.SimpConfig).toConfigCtx))
  else
    match configStx? with
    | none => `(tactic| simp at *)
    | some cfg =>
      `(tactic| simp (config := ($cfg : Aesop.SimpConfig).toConfig) at *)

def mkNormSimpOnlySyntax (inGoal : MVarId) (normSimpUseHyps : Bool)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    MetaM Syntax.Tactic := do
  let originalStx ← mkNormSimpSyntax normSimpUseHyps configStx?
  let includeFVars := ! normSimpUseHyps
  let stx ← inGoal.withContext do
    mkSimpOnly originalStx usedTheorems (includeFVars := includeFVars)
  return ⟨stx⟩

def mkNormSimpContext (rs : RuleSet) (simpConfig : Aesop.SimpConfig) :
    MetaM Simp.Context :=
  return {
    ← Simp.Context.mkDefault with
    simpTheorems := #[rs.normSimpLemmas]
    config := simpConfig.toConfig
  }

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
