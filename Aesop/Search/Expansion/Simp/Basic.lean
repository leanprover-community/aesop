/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script

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

-- TODO move to core
deriving instance BEq for Simp.ConfigCtx

structure SimpConfig extends Simp.ConfigCtx where
  maxDischargeDepth := 1
  useHyps := true
  deriving BEq

variable [Monad m] [MonadQuotation m] [MonadError m]

-- TODO copy-pasta from Lean.Elab.Tactic.traceSimpCall
-- NOTE: Must be executed in the context of the goal on which `simp` was run.
-- `stx` is the syntax of the original `simp`/`simp_all`/`simp?`/`simp_all?`
-- call.
def mkSimpOnly (stx : Syntax) (usedSimps : UsedSimps) : MetaM Syntax := do
  let mut stx := stx
  if stx[3].isNone then
    stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
  let mut args : Array Syntax := #[]
  let mut localsOrStar := some #[]
  let lctx ← getLCtx
  let env ← getEnv
  for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
    match thm with
    | .decl declName => -- global definitions in the environment
      if env.contains declName && !Lean.Elab.Tactic.simpOnlyBuiltins.contains declName then
        args := args.push (← `(Parser.Tactic.simpLemma| $(mkIdent (← unresolveNameGlobal declName)):ident))
    | .fvar fvarId => -- local hypotheses in the context
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

-- NOTE: the `Syntax`s produced by this function do not include the Aesop simp
-- set. This doesn't matter if we feed them into `mkSimpOnly`, but it would
-- matter if we were to execute them.
--
-- TODO this way to handle (config := ...) is ugly.
def mkNormSimpSyntax (normSimpUseHyps : Bool)
    (configStx? : Option Term) : MetaM Syntax.Tactic := do
  if normSimpUseHyps then
    match configStx? with
    | none => `(tactic| simp_all (config := ({} : Aesop.SimpConfig).toConfigCtx))
    | some cfg =>
      `(tactic| simp_all (config := ($cfg : Aesop.SimpConfig).toConfigCtx))
  else
    match configStx? with
    | none => `(tactic| simp (config := ({} : Aesop.SimpConfig).toConfig) at *)
    | some cfg =>
      `(tactic| simp (config := ($cfg : Aesop.SimpConfig).toConfig) at *)

-- FIXME minimised simp (`simp only`) does not work reliably
def mkNormSimpOnlySyntax (inGoal : MVarId) (normSimpUseHyps : Bool)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    MetaM Syntax.Tactic := do
  let originalStx ← mkNormSimpSyntax normSimpUseHyps configStx?
  let stx ← inGoal.withContext do mkSimpOnly originalStx usedTheorems
  return ⟨stx⟩

end Aesop
