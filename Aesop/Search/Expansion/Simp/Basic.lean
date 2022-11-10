/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

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

structure SimpConfig extends Simp.ConfigCtx where
  maxDischargeDepth := 1
  useHyps := true

variable [Monad m] [MonadQuotation m] [MonadError m]

-- NOTE: This is necessarily best-effort since the simp set can contain lemmas
-- which we can't represent as `simp only` arguments.
open Lean.Parser.Tactic in
def mkSimpOnlyTheorems (goalBeforeSimp : MVarId) (usedTheorems : UsedSimps) :
    MetaM (Array (TSyntax ``simpLemma)) :=
  goalBeforeSimp.withContext do
    usedTheorems.foldM (init := Array.mkEmpty usedTheorems.size) λ r origin _ => do
      match origin with
      | .decl name => return r.push $ ← `(simpLemma| $(mkIdent name):ident)
      | .fvar fvarId =>
        if let some ldecl ← fvarId.findDecl? then
          if ! ldecl.userName.hasMacroScopes then
            return r.push $ ← `(simpLemma| $(mkIdent $ ldecl.userName):ident)
          else
            return r
        else
          return r
      | .stx _ stx => return r.push ⟨stx⟩
      | .other _ => return r

end Aesop
