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
  ofGlobalRuleBuilder builderName λ phase decl => do
    try {
      let thms : SimpTheorems := {}
      let thms ← thms.addDeclToUnfold decl
      return .globalSimp {
        builder := builderName
        entries := thms.simpEntries
      }
    } catch e => {
      throwError "aesop: unfold builder: exception while trying to add {decl} as declaration to unfold:{indentD e.toMessageData}"
    }
  where
    builderName := BuilderName.unfold

def normSimpLemmas : RuleBuilder := λ input => do
  match input.kind with
  | .global decl =>
    try {
      let thms : SimpTheorems := {}
      let thms ← thms.addConst decl
      return .global $ .globalSimp {
        builder := builderName
        entries := thms.simpEntries
      }
    } catch e => {
      throwError "aesop: simp builder: exception while trying to add {decl} as a simp theorem:{indentD e.toMessageData}"
    }
  | .«local» originalFVarUserName goal =>
    let (goal, hyp) ← copyRuleHypothesis goal originalFVarUserName
    withMVarContext goal do
      let ldecl ← getLocalDecl hyp
      let type := ldecl.type
      unless ← isProp type do
        throwError "aesop: simp builder: simp rules must be propositions but {originalFVarUserName} has type{indentExpr type}"
      return .«local» goal $ .localSimp {
        builder := builderName
        originalFVarUserName
        copiedFVarUserName := (← getLocalDecl hyp).userName
      }
  where
    builderName := BuilderName.simp

end Aesop.RuleBuilder
