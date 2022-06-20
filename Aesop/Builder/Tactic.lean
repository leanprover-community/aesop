/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM)

namespace Aesop

structure TacticBuilderOptions extends RegularBuilderOptions where
  usesBranchState : Bool
  deriving Inhabited

protected def TacticBuilderOptions.default : TacticBuilderOptions where
  toRegularBuilderOptions := RegularBuilderOptions.default
  usesBranchState := true

def RuleBuilder.tactic (opts : TacticBuilderOptions) : RuleBuilder :=
  ofGlobalRuleBuilder builderName λ _ decl => do
    let type := (← getConstInfo decl).type
    if ← isDefEq (mkApp (mkConst ``TacticM) (mkConst ``Unit)) type then
      mkResult $ .tacticM decl
    else if ← isDefEq (mkConst ``SimpleRuleTac) type then
      mkResult $ .simpleRuleTac decl
    else if ← isDefEq (mkConst ``RuleTac) type then
      mkResult $ .ruleTac decl
    else
      throwError "aesop: {decl} was expected to be a tactic, i.e. to have one of these types:\n  TacticM Unit\n  SimpleRuleTac\n  RuleTac\nHowever, it has type{indentExpr type}"
  where
    builderName : BuilderName :=
      .tactic

    mkResult (tac : RuleTacDescr) : MetaM RuleBuilderResult :=
      return .regular {
        builder := builderName
        indexingMode := ← opts.getIndexingModeM $ pure IndexingMode.unindexed
        mayUseBranchState := opts.usesBranchState
        tac
      }

end Aesop
