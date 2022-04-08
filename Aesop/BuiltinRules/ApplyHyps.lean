/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

namespace Aesop.BuiltinRules

open Lean
open Lean.Meta

def applyHyp (hyp : FVarId) (previousMVars : Array MVarId) (goal : MVarId) :
    MetaM RuleApplication := do
  let goals ← apply goal (mkFVar hyp)
  let postState ← saveState
  let (goals, introducedMVars) ← getProperGoalsAndNewMVars previousMVars goals
  let assignedMVars ← getAssignedMVars previousMVars
  return { postState, goals, introducedMVars, assignedMVars }
  -- TODO optimise mvar analysis

@[aesop unsafe 75% (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def applyHyps : RuleTac := λ input =>
  withMVarContext input.goal do
    let lctx ← getLCtx
    let mut rapps := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isAuxDecl then continue
      let initialState ← saveState
      try
        let rapp ← applyHyp localDecl.fvarId input.mvars input.goal
        rapps := rapps.push rapp
      catch _ => continue
      finally restoreState initialState
    return {
      applications := rapps
      postBranchState? := none
    }

end Aesop.BuiltinRules
