/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

namespace Aesop.BuiltinRules

open Lean
open Lean.Meta

def applyHyp (hyp : FVarId) (goal : MVarId) (md : TransparencyMode)
    (generateScript : Bool) : MetaM RuleApplication :=
  goal.withContext do
    let goals := (← withTransparency md $ goal.apply (mkFVar hyp)).toArray
    let postState ← saveState
    let scriptBuilder? := mkScriptBuilder? generateScript $
      .ofTactic goals.size $ withTransparencySyntax md $
        ← `(tactic| apply $(mkIdent $ ← hyp.getUserName))
    return {
      successProbability? := none
      postState, goals, scriptBuilder?
    }

@[aesop unsafe 75% tactic (rule_sets [builtin])]
def applyHyps : RuleTac := λ input =>
  input.goal.withContext do
    let lctx ← getLCtx
    let generateScript := input.options.generateScript
    let md := input.options.applyHypsTransparency
    let mut rapps := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isImplementationDetail then continue
      let initialState ← saveState
      try
        let rapp ← applyHyp localDecl.fvarId input.goal md generateScript
        rapps := rapps.push rapp
      catch _ => continue
      finally restoreState initialState
    return ⟨rapps⟩

end Aesop.BuiltinRules
