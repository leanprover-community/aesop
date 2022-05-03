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

structure TacticBuilderOptions where
  usesBranchState : Bool
  deriving Inhabited

def TacticBuilderOptions.default : TacticBuilderOptions where
  usesBranchState := true

def RuleBuilder.tactic (opts : TacticBuilderOptions) : RuleBuilder :=
  ofGlobalRuleBuilder builderName λ phase decl => do
    let type := (← getConstInfo decl).type
    if ← isDefEq (mkApp (mkConst ``TacticM) (mkConst ``Unit)) type then
      return mkResult $ .tacticM decl
    else if ← isDefEq (mkConst ``SimpleRuleTac) type then
      return mkResult $ .simpleRuleTac decl
    else if ← isDefEq (mkConst ``RuleTac) type then
      return mkResult $ .ruleTac decl
    else
      throwError "aesop: {decl} was expected to be a tactic, i.e. to have one of these types:\n  TacticM Unit\n  SimpleRuleTac\n  RuleTac\nHowever, it has type{indentExpr type}"
  where
    builderName : BuilderName :=
      .tactic

    mkResult (tac : RuleTacDescr) : RuleBuilderResult :=
      .regular {
        builder := builderName
        tac
        indexingMode := IndexingMode.unindexed
        mayUseBranchState := opts.usesBranchState
      }

end Aesop
