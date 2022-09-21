/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop norm -100 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def intros : RuleTac := RuleTac.ofSingleRuleTac λ input => do
    let (newFVars, goal) ← unhygienic $ input.goal.intros
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    goal.withContext do
      let newFVarUserNames ← newFVars.mapM (mkIdent <$> ·.getUserName)
      let scriptBuilder :=
        .ofTactic 1 `(tactic| intro $newFVarUserNames:ident*)
      return (#[goal], scriptBuilder)

end Aesop.BuiltinRules
