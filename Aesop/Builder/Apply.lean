/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleTac

def applyConst (decl : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input => do
  let goals ← apply input.goal (← mkConstWithFreshMVarLevels decl)
  return {
    introducedMVars := IntroducedMVars.raw goals.toArray
    assignedMVars? := none
  }
  -- TODO optimise mvar analysis

def applyFVar (userName : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input =>
  withMVarContext input.goal do
    let decl ← getLocalDeclFromUserName userName
    let goals ← apply input.goal (mkFVar decl.fvarId)
    return {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
  -- TODO optimise mvar analysis

-- Tries to apply each constant in `decls`. For each one that applies, a rule
-- application is returned. If none applies, the tactic fails.
def applyConsts (decls : Array Name) : RuleTac := λ input => do
  let goal := input.goal
  let apps ← decls.filterMapM λ decl => observing? do
    let goals ← apply input.goal (← mkConstWithFreshMVarLevels decl)
    let postState ← saveState
    let rapp := {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
    return (rapp, postState)
  if apps.isEmpty then
    failure
  return { applications := apps, postBranchState? := none }

end RuleTac


def GlobalRuleTacBuilder.apply (decl : Name) : GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.applyConst decl
    descr := GlobalRuleTacBuilderDescr.apply decl
  }

def RuleTacBuilder.applyFVar (userName : Name) : RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← RuleTacBuilder.copyRuleHypotheses goal #[userName] |
    unreachable!
  withMVarContext goal do
    let tac :=
      { tac := RuleTac.applyFVar (← getLocalDecl newHyp).userName
        descr := none }
    return (goal, tac)

def GlobalRuleBuilder.apply :
    GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  return {
    builder := BuilderName.apply
    tac := ← GlobalRuleTacBuilder.apply decl
    indexingMode := ←
      IndexingMode.targetMatchingConclusion (← getConstInfo decl).type
    mayUseBranchState := false
  }

def LocalRuleBuilder.apply :
    LocalRuleBuilder RegularRuleBuilderResult := λ hypUserName goal => do
  let (goal, tac) ← RuleTacBuilder.applyFVar hypUserName goal
  withMVarContext goal do
    let type := (← getLocalDeclFromUserName hypUserName).type
    let result := {
      builder := BuilderName.apply
      tac := tac
      indexingMode := ← IndexingMode.targetMatchingConclusion type
      mayUseBranchState := false
    }
    return (goal, result)

def RuleBuilder.apply : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.apply LocalRuleBuilder.apply

end Aesop
