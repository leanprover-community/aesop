/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule
import Lean

open Lean
open Lean.Meta

namespace Aesop

structure RegularRuleBuilderResult where
  builder : BuilderName
  tac : RuleTacWithBuilderDescr
  indexingMode : IndexingMode
  mayUseBranchState : Bool
  deriving Inhabited

structure SimpRuleBuilderResult where
  builder : BuilderName
  entries : Array SimpEntry

inductive NormRuleBuilderResult
  | regular (r : RegularRuleBuilderResult)
  | simp (r : SimpRuleBuilderResult)
  deriving Inhabited

/--
A `GlobalRuleBuilder` takes the name of a global constant and produces a
`RegularRuleBuilderResult` or `NormRuleBuilderResult`.
-/
abbrev GlobalRuleBuilder α := Name → MetaM α

/--
A `LocalRuleBuilder` takes the `userName` of a hypothesis and produces a
`RegularRuleBuilderResult` or `NormRuleBuilderResult`. It operates on the given
goal and may change it.
-/
abbrev LocalRuleBuilder α := Name → MVarId → MetaM (MVarId × α)

/--
A `RuleBuilder` is either a `GobalRuleBuilder` or a `LocalRuleBuilder`
-/
abbrev RuleBuilder α := RuleIdent → MVarId → MetaM (MVarId × α)

namespace GlobalRuleBuilder

def checkConstIsInductive (builderName : Name) (decl : Name) :
    MetaM InductiveVal := do
  let (some info) ← getConst? decl
    | throwError "aesop: {builderName} builder: unknown constant '{decl}'"
  let (ConstantInfo.inductInfo info) ← pure info
    | throwError "aesop: {builderName} builder: expected '{decl}' to be an inductive type"
  return info

end GlobalRuleBuilder


namespace RuleBuilder

def toGlobalRuleBuilder (r : RuleBuilder α) : GlobalRuleBuilder α := λ decl =>
  Prod.snd <$> r (RuleIdent.const decl) ⟨`_aesop_rule_builder_dummy⟩
  -- NOTE: We assume that the 'global part' of `r` does not use the `_dummy`
  -- mvar.

def toLocalRuleBuilder (r : RuleBuilder α) :
    LocalRuleBuilder α := λ fvarId goal =>
  r (RuleIdent.fvar fvarId) goal

def toNormRuleBuilder (r : RuleBuilder RegularRuleBuilderResult) :
    RuleBuilder NormRuleBuilderResult := λ id goal => do
  let (goal, res) ← r id goal
  return (goal, NormRuleBuilderResult.regular res)

def ofGlobalAndLocalRuleBuilder (global : GlobalRuleBuilder α)
    («local» : LocalRuleBuilder α) : RuleBuilder α := λ id goal => do
  match id with
  | RuleIdent.const const => return (goal, ← global const)
  | RuleIdent.fvar hyp => «local» hyp goal

def ofGlobalRuleBuilder (builderName : String) (global : GlobalRuleBuilder α) :
    RuleBuilder α :=
  ofGlobalAndLocalRuleBuilder global
    (λ _ _ => throwError
      "aesop: {builderName} builder: this builder does not support local hypotheses")

end Aesop.RuleBuilder
