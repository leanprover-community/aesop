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

def RuleBuilder.tactic : RuleBuilder := λ input => do
  let opts := input.options
  let decl ← input.getGlobalRuleIdent .tactic
  let imode ← opts.getIndexingModeM $ pure IndexingMode.unindexed
  let type := (← getConstInfo decl).type
  let tac ←
    if ← isDefEq (mkApp (mkConst ``TacticM) (mkConst ``Unit)) type then
      pure $ .tacticM decl
    else if ← isDefEq (mkConst ``SingleRuleTac) type then
      pure $ .singleRuleTac decl
    else if ← isDefEq (mkConst ``RuleTac) type then
      pure $ .ruleTac decl
    else if ← isDefEq (mkConst ``TacGen) type then
      pure $ .tacGen decl
    else
      throwError "aesop: {decl} was expected to be a tactic, i.e. to have one of these types:\n  TacticM Unit\n  SimpleRuleTac\n  RuleTac\n  TacGen\nHowever, it has type{indentExpr type}"
  return .global $ .base $ input.toRule .tactic imode tac

end Aesop
