/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

def apply : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global decl => do
    let tac := .applyConst decl
    let type := (← getConstInfo decl).type
    RuleBuilderOutput.global <$> mkResult tac type
  | RuleBuilderKind.local fvarUserName goal => do
    let (goal, newHyp) ← copyRuleHypothesis goal fvarUserName
    withMVarContext goal do
      let decl ← getLocalDecl newHyp
      let tac := RuleTacDescr.applyFVar decl.userName
      let result ← mkResult tac decl.type
      return RuleBuilderOutput.local goal result
  where
    mkResult (tac : RuleTacDescr) (type : Expr) : MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.apply
        tac := tac
        indexingMode := ← IndexingMode.targetMatchingConclusion type
        mayUseBranchState := false
      }

end Aesop.RuleBuilder
