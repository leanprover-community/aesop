/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop.BuiltinRules

@[aesop safe -50 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def assumption : RuleTac := λ input => do
  let goal := input.goal
  withMVarContext goal do
    checkNotAssigned goal `Aesop.BuiltinRules.assumption
    let tgt ← instantiateMVarsInMVarType goal
    let initialState ← saveState
    let mut applications := #[]
    for ldecl in ← getLCtx do
      if ldecl.isAuxDecl then
        continue
      restoreState initialState
      let (some (application, proofHasMVar)) ←
        tryHyp goal tgt ldecl
        | continue
      if ! tgt.hasMVar && ! proofHasMVar then
        applications := #[application]
        break
      else
        applications := applications.push application
    if applications.isEmpty then
      throwTacticEx `Aesop.BuiltinRules.assumption goal "no matching assumption found"
    return {
      applications
      postBranchState? := none
    }
  where
    tryHyp (goal : MVarId) (tgt : Expr) (ldecl : LocalDecl) :
        MetaM (Option (RuleApplication × Bool)) := do
      let proofHasMVar := ldecl.type.hasMVar
      if ! (← isDefEq ldecl.type tgt) then
        return none
      assignExprMVar goal ldecl.toExpr
      let postState ← saveState
      let app := {
        goals := #[]
        postState
      }
      return some (app, proofHasMVar)

end Aesop.BuiltinRules
