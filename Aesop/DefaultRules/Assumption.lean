/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac

open Lean
open Lean.Meta

namespace Aesop.DefaultRules

def findLocalDeclWithMVarFreeType? (goal : MVarId) (type : Expr) :
    MetaM (Option FVarId) :=
  withMVarContext goal do
    (← getMVarDecl goal).lctx.findDeclRevM? λ localDecl => do
        if localDecl.isAuxDecl then return none
        let localType ← instantiateMVarsInLocalDeclType goal localDecl.fvarId
        if localType.hasMVar then
          return none
        else if (← isDefEq type localType) then
          return some localDecl.fvarId
        else
          return none

def assumption : RuleTac := λ { goal, .. } =>
  withMVarContext goal do
    checkNotAssigned goal `Aesop.DefaultRules.assumption
    let tgt ← instantiateMVarsInMVarType goal
    if tgt.hasMVar then
      throwTacticEx `Aesop.DefaultRules.assumption goal "target contains metavariables"
    let hyp? ← findLocalDeclWithMVarFreeType? goal tgt
    match hyp? with
    | none => throwTacticEx `Aesop.DefaultRules.assumption goal "no matching assumption found"
    | some hyp => do
      assignExprMVar goal (mkFVar hyp)
      let postState ← saveState
      let ro := {
        regularGoals := #[]
        unificationGoals := #[]
        postState := postState
      }
      return #[ro]

end Aesop.DefaultRules
