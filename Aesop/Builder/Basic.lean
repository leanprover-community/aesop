/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleSet.Member

open Lean Lean.Meta Lean.Elab.Term

namespace Aesop

/--
Options for the builders. Most options are only relevant for certain builders.
-/
structure RuleBuilderOptions where
  immediatePremises? : Option (Array Name)
  indexingMode? : Option IndexingMode
  casesPatterns? : Option (Array CasesPattern)
  pattern? : Option RulePattern
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

def getIndexingModeM [Monad m] (dflt : m IndexingMode)
    (opts : RuleBuilderOptions) : m IndexingMode :=
  match opts.indexingMode? with
  | none => dflt
  | some imode => return imode

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
  ident : RuleIdent
  options : RuleBuilderOptions
  extra : ExtraRuleBuilderInput
  deriving Inhabited

namespace RuleBuilderInput

def phase (input : RuleBuilderInput) : PhaseName :=
  input.extra.phase

def toRuleName (builder : BuilderName)
    (input : RuleBuilderInput) : RuleName :=
  input.ident.toRuleName input.phase builder

def getGlobalRuleIdent [Monad m] [MonadError m] (builderName : BuilderName)
    (input : RuleBuilderInput) : m Name :=
  if let some decl := input.ident.const? then
    return decl
  else
    throwError "aesop: {builderName} builder does not support local rules"

def getInductiveRuleIdent [Monad m] [MonadError m] [MonadEnv m]
    (builderName : BuilderName) (input : RuleBuilderInput) :
    m InductiveVal := do
  let decl ← input.getGlobalRuleIdent builderName
  let info ← getConstInfo decl
    <|> throwError "aesop: {builderName} builder: unknown constant '{decl}'"
  let (ConstantInfo.inductInfo info) ← pure info
    | throwError "aesop: {builderName} builder: expected '{decl}' to be an inductive type"
  return info

def toRule (builder : BuilderName) (indexingMode : IndexingMode)
    (tac : RuleTacDescr) (input : RuleBuilderInput) : BaseRuleSetMember :=
  let name := input.toRuleName builder
  let pattern? := input.options.pattern?
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


abbrev RuleBuilder := RuleBuilderInput → TermElabM LocalRuleSetMember
