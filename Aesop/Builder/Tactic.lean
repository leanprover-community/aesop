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

namespace GlobalRuleTacBuilder

private def checkDeclType (expectedType : Expr) (decl : Name) : MetaM Unit := do
  let actualType := (← getConstInfo decl).type
  unless (← isDefEq expectedType actualType) do
    throwError "aesop: {decl} was expected to have type{indentExpr expectedType}\nbut has type{indentExpr actualType}"

unsafe def tacticMUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  checkDeclType (← mkAppM ``TacticM #[mkConst ``Unit]) decl
  let tac := SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
      -- It is in principle possible for the environment to change so that
      -- `decl` has a different type at the point where this tactic is called.
      -- We assume that this doesn't happen. Ideally, we would evaluate `tac`
      -- directly after `checkDeclType`, but this fails when this function is
      -- called by the `@[aesop]` attribute.
    let goals ← runTacticMAsMetaM tac input.goal
    return {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.tacticM decl }

@[implementedBy tacticMUnsafe]
constant tacticM : Name → GlobalRuleTacBuilder

unsafe def ruleTacUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  checkDeclType (mkConst ``RuleTac) decl
  let tac := λ input => do (← evalConst RuleTac decl) input
    -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.ruleTac decl }

@[implementedBy ruleTacUnsafe]
constant ruleTac : Name → GlobalRuleTacBuilder

unsafe def simpleRuleTacUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  checkDeclType (mkConst ``SimpleRuleTac) decl
  let tac := SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SimpleRuleTac decl
      -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.
    tac input
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.simpleRuleTac decl }

@[implementedBy simpleRuleTacUnsafe]
constant simpleRuleTac : Name → GlobalRuleTacBuilder

def tactic (decl : Name) : GlobalRuleTacBuilder := do
  tacticM decl <|>
  simpleRuleTac decl <|>
  ruleTac decl <|>
  do throwError "aesop: {decl} was expected to be a tactic but it has type{indentExpr (← getConstInfo decl).type}"

end GlobalRuleTacBuilder


def RuleBuilder.tactic (opts : TacticBuilderOptions) : RuleBuilder :=
  ofGlobalRuleBuilder name λ phase decl =>
    return RuleBuilderResult.regular {
      builder := name
      tac := ← GlobalRuleTacBuilder.tactic decl
      indexingMode := IndexingMode.unindexed
      mayUseBranchState := opts.usesBranchState
    }
  where
    name := BuilderName.tactic

end Aesop
