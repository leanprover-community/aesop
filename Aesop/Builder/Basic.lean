/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.ElabM
import Aesop.Rule.Name
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

structure CoreRuleBuilderOutput where
  ruleExprName : Name
  builderName : BuilderName
  scopeName : ScopeName
  tac : RuleTacDescr
  indexingMode : IndexingMode
  pattern? : Option RulePattern

inductive PhaseSpec
  | safe (info : SafeRuleInfo)
  | norm (info : NormRuleInfo)
  | «unsafe» (info : UnsafeRuleInfo)
  deriving Inhabited

namespace PhaseSpec

def phase : PhaseSpec → PhaseName
  | safe .. => .safe
  | «unsafe» .. => .unsafe
  | norm .. => .norm

def toRule (phase : PhaseSpec) (ruleExprName : Name) (builder : BuilderName)
    (scope : ScopeName) (tac : RuleTacDescr) (indexingMode : IndexingMode)
    (pattern? : Option RulePattern) : BaseRuleSetMember :=
  let name := {
    name := ruleExprName
    phase := phase.phase
    builder, scope
  }
  match phase with
  | .safe info => .safeRule {
      extra := info
      name, indexingMode, pattern?, tac
    }
  | .unsafe info => .unsafeRule {
      extra := info
      name, indexingMode, pattern?, tac
    }
  | .norm info => .normRule {
      extra := info
      name, indexingMode, pattern?, tac
    }

end PhaseSpec


structure RuleBuilderInput where
  term : Term
  options : RuleBuilderOptions
  phase : PhaseSpec
  deriving Inhabited

namespace RuleBuilderInput

def phaseName (input : RuleBuilderInput) : PhaseName :=
  input.phase.phase

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
