/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

def normSimpUnfold : RuleBuilder :=
  ofGlobalRuleBuilder name λ phase decl => do
    try {
      let thms : SimpTheorems := {}
      let thms ← thms.addDeclToUnfold decl
      return RuleBuilderResult.simp {
        builder := name
        entries := thms.simpEntries
      }
    } catch e => {
      throwError "aesop: unfold builder: exception while trying to add {decl} as declaration to unfold:{indentD e.toMessageData}"
    }
  where
    name := BuilderName.unfold

def normSimpLemmas : RuleBuilder :=
  ofGlobalRuleBuilder name λ phase decl => do
    try {
      let thms : SimpTheorems := {}
      let thms ← thms.addConst decl
      return RuleBuilderResult.simp {
        builder := name
        entries := thms.simpEntries
      }
    } catch e => {
      throwError "aesop: simp builder: exception while trying to add {decl} as a simp lemma:{indentD e.toMessageData}"
    }
  where
    name := BuilderName.simp

end Aesop.RuleBuilder
