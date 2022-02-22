/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

namespace Aesop.BuiltinRules

open Lean
open Lean.Meta

def applyHyp (hyp : FVarId) (input : RuleTacInput) : MetaM RuleApplication := do
  let goals ← apply input.goal (mkFVar hyp)
  let output : SimpleRuleTacOutput := { goals := goals.toArray.map λ g => (g, none) }
  output.toRuleApplication
  -- TODO optimise ugoal analysis

@[aesop unsafe 75% (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def applyHyps : RuleTac := λ input =>
  withMVarContext input.goal do
    let lctx ← getLCtx
    let mut rapps := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isAuxDecl then continue
      let initialState ← saveState
      try
        let rapp ← applyHyp localDecl.fvarId input
        rapps := rapps.push rapp
      catch _ => continue
      finally restoreState initialState
    return {
      applications := rapps
      postBranchState? := none
    }

end Aesop.BuiltinRules
