/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Kyle Miller
-/

import Aesop.Frontend.Attribute
import Std.Tactic.OpenPrivate

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

open private getIntrosSize in Lean.MVarId.intros

/-- Introduce as many binders as possible while unfolding definitions with the
ambient transparency. -/
partial def introsUnfolding (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  run mvarId #[]
where
  run (mvarId : MVarId) (fvars : Array FVarId) : MetaM (Array FVarId × MVarId) :=
    mvarId.withContext do
      let type ← whnf (← mvarId.getType)
      let size := getIntrosSize type
      if 0 < size then
        let (fvars', mvarId') ← mvarId.introN size
        run mvarId' (fvars ++ fvars')
      else
        return (fvars, mvarId)

@[aesop norm -100 (rule_sets [builtin])]
def intros : RuleTac := RuleTac.ofSingleRuleTac λ input => do
    let md? := input.options.introsTransparency?
    let (newFVars, goal) ← unhygienic $
      if let some md := md? then
        withTransparency md $ introsUnfolding input.goal
      else
        input.goal.intros
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    let scriptBuilder? ←
      if input.options.generateScript then
        goal.withContext do
          let newFVarUserNames ← newFVars.mapM (mkIdent <$> ·.getUserName)
          let tac ← `(tactic| intro $newFVarUserNames:ident*)
          let tac :=
            if let some md := md? then
              withAllTransparencySyntax md tac
            else
              pure tac
          pure $ some $ .ofTactic 1 tac

      else
        pure none
    return (#[goal], scriptBuilder?, none)

end Aesop.BuiltinRules
