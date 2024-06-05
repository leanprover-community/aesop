/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

namespace Aesop.BuiltinRules

open Lean
open Lean.Meta

def applyHyp (hyp : FVarId) (goal : MVarId) (md : TransparencyMode) :
    MetaM RuleApplication := do
  let (step, _) ← applyS goal (.fvar hyp) none md
  return .ofLazyScriptStep step none

@[aesop unsafe 75% tactic (rule_sets := [builtin])]
def applyHyps : RuleTac := λ input =>
  input.goal.withContext do
    let lctx ← getLCtx
    let md := input.options.applyHypsTransparency
    let mut rapps := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isImplementationDetail then continue
      let initialState ← saveState
      try
        let rapp ← applyHyp localDecl.fvarId input.goal md
        rapps := rapps.push rapp
      catch _ => continue
      finally restoreState initialState
    return ⟨rapps⟩

end Aesop.BuiltinRules
