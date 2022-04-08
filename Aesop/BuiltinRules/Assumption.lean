/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

def findLocalDeclWithMVarFreeType? (goal : MVarId) (type : Expr) :
    MetaM (Option FVarId) :=
  withMVarContext goal do
    (← getLCtx).findDeclRevM? λ localDecl => do
        if localDecl.isAuxDecl then
          return none
        let localType ← instantiateMVarsInLocalDeclType goal localDecl.fvarId
        if ← pure ! localType.hasMVar <&&> isDefEq type localType then
          return some localDecl.fvarId
        else
          return none

@[aesop safe -50 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def safeAssumption : SimpleRuleTac := λ { goal, .. } =>
  withMVarContext goal do
    checkNotAssigned goal `Aesop.BuiltinRules.safeAssumption
    let tgt ← instantiateMVarsInMVarType goal
    if tgt.hasMVar then
      throwTacticEx `Aesop.BuiltinRules.safeAssumption goal "target contains metavariables"
    let hyp? ← findLocalDeclWithMVarFreeType? goal tgt
    match hyp? with
    | none => throwTacticEx `Aesop.BuiltinRules.safeAsumption goal "no matching assumption found"
    | some hyp => do
      assignExprMVar goal (mkFVar hyp)
      return []

end Aesop.BuiltinRules
