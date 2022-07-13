/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop (rule_sets [builtin]) safe 100 (tactic (uses_branch_state := false))]
def splitTarget : RuleTac := λ input => do
  let (some goals) ← splitTarget? input.goal | throwError
    "nothing to split in target"
  let postState ← saveState
  return {
    applications := #[{ goals := goals.toArray, postState }]
    postBranchState? := none
  }

def splitFirstHypothesis (goal : MVarId) : MetaM (Option (Array MVarId)) :=
  withMVarContext goal do
    for ldecl in ← getLCtx do
      if let some goals ← splitLocalDecl? goal ldecl.fvarId then
        return goals.toArray
    return none

def splitHypothesesCore (goal : MVarId) : MetaM (Option (Array MVarId)) :=
  saturate1 goal splitFirstHypothesis

@[aesop (rule_sets [builtin]) safe 1000 (tactic (uses_branch_state := false))]
def splitHypotheses : RuleTac := λ input => do
  let (some goals) ← splitHypothesesCore input.goal | throwError
    "no splittable hypothesis found"
  let postState ← saveState
  return {
    applications := #[{ goals, postState }]
    postBranchState? := none
  }

end Aesop.BuiltinRules
