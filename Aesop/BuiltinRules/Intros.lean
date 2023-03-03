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
  | .forallE _ _ b _ => return (← getIntrosSizeUnfolding b) + 1
  | .letE _ _ _ b _ => return (← getIntrosSizeUnfolding b) + 1
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

@[aesop norm -100 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def intros : RuleTac := RuleTac.ofSingleRuleTac λ input => do
    let (newFVars, goal) ← unhygienic $
      if let some md := input.options.introsTransparency? then
        withTransparency md $ introsUnfolding input.goal
      else
        input.goal.intros
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    let scriptBuilder? ←
      if input.options.generateScript then
        goal.withContext do
          let newFVarUserNames ← newFVars.mapM (mkIdent <$> ·.getUserName)
          pure $ some $ .ofTactic 1 `(tactic| intro $newFVarUserNames:ident*)
      else
        pure none
    return (#[goal], scriptBuilder?)

end Aesop.BuiltinRules
