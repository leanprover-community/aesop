/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

namespace Aesop.BuiltinRules

@[aesop safe -49 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def safeReflexivity : RuleTac := λ { goal, .. } => do
  withMVarContext goal do
    let tgt ← instantiateMVarsInMVarType goal
    if tgt.hasMVar then
      throwTacticEx `Aesop.BuiltinRules.safeReflexivity goal "target contains metavariables"
    let [] ← runTacticMAsMetaM (do evalTactic (← `(rfl))) goal
      | throwError "aesop: internal error: safeReflexivity: rfl did not close the goal"
    let postState ← saveState
    return {
      applications := #[{
        goals := #[]
        postState := postState
      }]
      postBranchState? := none
    }

end Aesop.BuiltinRules
