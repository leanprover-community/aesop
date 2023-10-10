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

def RuleBuilder.tactic (opts : RegularBuilderOptions) : RuleBuilder :=
  ofGlobalRuleBuilder builderName λ _ decl => do
    let type := (← getConstInfo decl).type
    if ← isDefEq (mkApp (mkConst ``TacticM) (mkConst ``Unit)) type then
      mkResult $ .tacticM decl
    else if ← isDefEq (mkConst ``SingleRuleTac) type then
      mkResult $ .singleRuleTac decl
    else if ← isDefEq (mkConst ``RuleTac) type then
      mkResult $ .ruleTac decl
    else if ← isDefEq (mkConst ``TacGen) type then
      mkResult $ .tacGen decl
    else
      throwError "aesop: {decl} was expected to be a tactic, i.e. to have one of these types:\n  TacticM Unit\n  SimpleRuleTac\n  RuleTac\n  TacGen\nHowever, it has type{indentExpr type}"
  where
    builderName : BuilderName :=
      .tactic

    mkResult (tac : RuleTacDescr) : MetaM RuleBuilderResult :=
      return .regular {
        builder := builderName
        indexingMode := ← opts.getIndexingModeM $ pure IndexingMode.unindexed
        tac
      }

end Aesop
