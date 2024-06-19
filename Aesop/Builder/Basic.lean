/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.ElabM
import Aesop.RuleSet.Member
import Aesop.RuleTac.ElabRuleTerm

open Lean Lean.Meta Lean.Elab.Term

namespace Aesop

/--
Options for the builders. Most options are only relevant for certain builders.
-/
structure RuleBuilderOptions where
  immediatePremises? : Option (Array Name)
  indexingMode? : Option IndexingMode
  casesPatterns? : Option (Array CasesPattern)
  pattern? : Option Term
  /-- The transparency used by the rule tactic. -/
  transparency? : Option TransparencyMode
  /-- The transparency used for indexing the rule. Currently, the rule is not
  indexed unless this is `.reducible`. -/
  indexTransparency? : Option TransparencyMode
  deriving Inhabited

namespace RuleBuilderOptions

protected def default : RuleBuilderOptions :=
  ⟨none, none, none, none, none, none⟩

instance : EmptyCollection RuleBuilderOptions :=
  ⟨.default⟩

end RuleBuilderOptions


inductive ExtraRuleBuilderInput
  | safe (penalty : Int) (safety : Safety)
  | norm (penalty : Int)
  | «unsafe» (successProbability : Percent)
  deriving Inhabited

def ExtraRuleBuilderInput.phase : ExtraRuleBuilderInput → PhaseName
  | safe .. => .safe
  | «unsafe» .. => .unsafe
  | norm .. => .norm


structure RuleBuilderInput where
  term : Term
  options : RuleBuilderOptions
  extra : ExtraRuleBuilderInput
  deriving Inhabited

namespace RuleBuilderInput

def phase (input : RuleBuilderInput) : PhaseName :=
  input.extra.phase

def toRule (builder : BuilderName) (name : Name) (scope : ScopeName)
    (tac : RuleTacDescr) (indexingMode : IndexingMode)
    (pattern? : Option RulePattern) (input : RuleBuilderInput) :
    BaseRuleSetMember :=
  let name := { name, builder, scope, phase := input.phase }
  match input.extra with
  | .safe penalty safety => .safeRule {
      extra := { penalty, safety }
      name, indexingMode, tac, pattern?
    }
  | .unsafe successProbability => .unsafeRule {
      extra := { successProbability }
      name, indexingMode, tac, pattern?
    }
  | .norm penalty => .normRule {
      extra := { penalty }
      name, indexingMode, tac, pattern?
    }

end RuleBuilderInput


abbrev RuleBuilder := RuleBuilderInput → ElabM LocalRuleSetMember


def elabGlobalRuleIdent (builderName : BuilderName) (term : Term) :
    TermElabM Name := do
  if let some decl ← elabGlobalRuleIdent? term then
    return decl
  else
    throwError "aesop: {builderName} builder: expected '{term}' to be an unambiguous global constant"

def elabInductiveRuleIdent (builderName : BuilderName) (term : Term) :
    TermElabM InductiveVal := do
  if let some info ← elabInductiveRuleIdent? term then
    return info
  else
    throwError "aesop: {builderName} builder: expected '{term}' to be an inductive type or structure"

end Aesop
