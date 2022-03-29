/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.GlobalRuleBuilder

-- TODO We currently don't process unfold theorems and smart unfolding equations
-- (whatever that is). See SimpLemmas.lean:mkSimpAttr.
def normSimpUnfold : GlobalRuleBuilder NormRuleBuilderResult := λ decl => do
  let info ← getConstInfo decl
  unless info.hasValue do
    throwError "aesop: unfold builder: expected {decl} to be a definition to unfold"
  return NormRuleBuilderResult.simp
    { builder := BuilderName.unfold, entries := #[SimpEntry.toUnfold decl] }

def normSimpLemmas : GlobalRuleBuilder NormRuleBuilderResult := λ decl => do
  try {
    let simpLemmas ←
      mkSimpTheoremsFromConst decl (post := true) (inv := false) (prio := 0)
    return NormRuleBuilderResult.simp {
      builder := BuilderName.simp
      entries := simpLemmas.map SimpEntry.thm
    }
  } catch e => {
    throwError "aesop: simp builder: exception while trying to add {decl} as a simp lemma:{indentD e.toMessageData}"
  }

end GlobalRuleBuilder


namespace RuleBuilder

def normSimpUnfold : RuleBuilder NormRuleBuilderResult :=
  ofGlobalRuleBuilder "unfold" GlobalRuleBuilder.normSimpUnfold

def normSimpLemmas : RuleBuilder NormRuleBuilderResult :=
  ofGlobalRuleBuilder "simp" GlobalRuleBuilder.normSimpLemmas

end Aesop.RuleBuilder
