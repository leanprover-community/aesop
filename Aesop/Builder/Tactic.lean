/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean Lean.Meta
open Lean.Elab.Tactic (TacticM)
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop

def matchByTactic? : Term → Option (TSyntax ``tacticSeq)
  | `(by $ts:tacticSeq) => some ts
  | _ => none

namespace RuleBuilder

def tacticIMode (imode? : Option IndexingMode) : IndexingMode :=
  imode?.getD .unindexed

def tacticCore (t : Sum Name (TSyntax ``tacticSeq)) (imode? : Option IndexingMode) (phase : PhaseSpec) :
    MetaM LocalRuleSetMember := do
  let imode := imode?.getD .unindexed
  match t with
  | .inl decl =>
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
        throwError "aesop: tactic builder: expected {decl} to be a tactic, i.e. to have one of these types:\n  TacticM Unit\n  SimpleRuleTac\n  RuleTac\n  TacGen\nHowever, it has type{indentExpr type}"
    return .global $ .base $ phase.toRule decl .tactic .global tac imode none
  | .inr tacticSeq =>
    let name ← mkFreshId
    let tac := .tacticStx tacticSeq
    return .global $ .base $ phase.toRule name .tactic .global tac imode none

def tactic : RuleBuilder := λ input => do
  let opts := input.options
  let t ←
    if input.term.raw.isIdent then
      .inl <$> elabGlobalRuleIdent .tactic input.term
    else if let some stx := matchByTactic? input.term then
      pure $ .inr stx
    else
      throwError "aesop: tactic builder: expected '{input.term}' to be a tactic"
  tacticCore t opts.indexingMode? input.phase

end Aesop.RuleBuilder
