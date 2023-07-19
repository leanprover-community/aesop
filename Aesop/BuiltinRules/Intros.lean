/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

partial def getIntrosSizeUnfolding : Expr → MetaM Nat
  | .forallE n t b bi =>
    withLocalDecl n bi t λ fvar =>
      return (← getIntrosSizeUnfolding $ b.instantiate1 fvar) + 1
    -- Repeated `instantiate1` is not very efficient, but probably good enough.
  | .letE n t v b _ =>
    withLetDecl n t v λ fvar =>
      return (← getIntrosSizeUnfolding $ b.instantiate1 fvar) + 1
  | .mdata _ b => getIntrosSizeUnfolding b
  | e => do
    let e' ← whnf e
    if e' == e then
      return 0
    else
      getIntrosSizeUnfolding e'

def introsUnfolding (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← instantiateMVars (← mvarId.getType)
  let n ← getIntrosSizeUnfolding type
  mvarId.introN n

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
    return (#[goal], scriptBuilder?)

end Aesop.BuiltinRules
