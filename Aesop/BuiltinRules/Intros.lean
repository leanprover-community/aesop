/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Kyle Miller
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop norm -100 (rule_sets := [builtin])]
def intros : RuleTac := RuleTac.ofSingleRuleTac λ input => do
    let md? := input.options.introsTransparency?
    let ((goal, newFVarIds), steps) ←
      match md? with
      | none => introsS input.goal |>.run
      | some md => introsUnfoldingS input.goal md |>.run
    if newFVarIds.size == 0 then
      throwError "nothing to introduce"
    let addedFVars := newFVarIds.foldl (init := ∅) λ set fvarId =>
      set.insert fvarId
    let diff := { addedFVars, removedFVars := ∅, fvarSubst := ∅ }
    return (#[{ mvarId := goal, diff }], steps, none)

end Aesop.BuiltinRules
