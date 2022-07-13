/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop norm -100 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def intros : RuleTac := λ input => do
    let (newFVars, goal) ← Meta.intros input.goal
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    let postState ← saveState
    return {
      applications := #[{ goals := #[goal], postState }]
      postBranchState? := none
    }

end Aesop.BuiltinRules
