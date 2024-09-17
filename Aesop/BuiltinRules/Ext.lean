/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

namespace Aesop.BuiltinRules

open Lean Lean.Meta

def extCore (goal : MVarId) : ScriptM (Option (Array MVarId)) :=
  saturate1 goal λ goal => do
    let r ← straightLineExtS goal
    if r.depth == 0 then
      return none
    else
      return r.goals.map (·.1)

@[aesop 80% tactic (index := [target _ = _]) (rule_sets := [builtin])]
def ext : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals, steps) ← extCore input.goal |>.run
    | throwError "found no applicable ext lemma"
  let goals ← goals.mapM (mvarIdToSubgoal (parentMVarId := input.goal) · ∅)
  return (goals, steps, none)

end Aesop.BuiltinRules
