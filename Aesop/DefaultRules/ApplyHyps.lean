/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac

namespace Aesop.DefaultRules

open Lean
open Lean.Meta

def applyHyp (hyp : FVarId) (input : RuleTacInput) : MetaM RuleTacOutput := do
  let goals ← apply input.goal (mkFVar hyp)
  UserRuleTacOutput.toRuleTacOutput { regularGoals := goals.toArray }

def applyHyps : RuleTac := λ input =>
  withMVarContext input.goal do
    let lctx ← getLCtx
    let mut outputs := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isAuxDecl then continue
      let initialState ← saveState
      try
        let output ← applyHyp localDecl.fvarId input
        outputs := outputs.push output
      catch _ => continue
      finally restoreState initialState
    return outputs

end Aesop.DefaultRules
