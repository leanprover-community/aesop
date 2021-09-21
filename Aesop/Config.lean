/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.RuleSet
import Aesop.RuleBuilder
import Aesop.Options

open Lean
open Lean.Meta
open Lean.Elab.Term

namespace Aesop

namespace Parser.Attribute

declare_syntax_cat aesop_prio

syntax "-"? num "%"? : aesop_prio

declare_syntax_cat' aesop_kind force_leading_unreserved_tokens

syntax (aesop_prio)? : aesop_kind
syntax &"safe" (aesop_prio)? : aesop_kind
syntax &"unsafe" (aesop_prio)? : aesop_kind
syntax &"norm" (aesop_prio)? : aesop_kind

declare_syntax_cat' aesop_builder force_leading_unreserved_tokens

syntax &"apply" : aesop_builder
syntax &"simp" : aesop_builder
syntax &"unfold" : aesop_builder
syntax &"tactic" : aesop_builder
syntax &"constructors" : aesop_builder
syntax &"safe_default" : aesop_builder
syntax &"unsafe_default" : aesop_builder
syntax &"norm_default" : aesop_builder

declare_syntax_cat' aesop_clause

syntax "(" &"builder" aesop_builder ")" : aesop_clause
syntax "(" &"options" term ")" : aesop_clause

syntax (name := aesop) &"aesop" aesop_kind aesop_clause* : attr

end Parser.Attribute


variable [Monad m] [MonadError m]


inductive Prio
  | successProbability (p : Percent)
  | penalty (i : Int)
  deriving Inhabited, BEq

namespace Prio

instance : ToString Prio where
  toString
    | successProbability p => p.toHumanString
    | penalty i => toString i

protected def parse : Syntax → Except String Prio
  | `(aesop_prio|- $n:numLit %) =>
    throw "percentage cannot be negative"
  | `(aesop_prio|- $n:numLit) => return penalty $ - n.toNat
  | `(aesop_prio|$n:numLit) => return penalty $ n.toNat
  | `(aesop_prio|$n:numLit %) => do
    let (some p) ← Percent.ofNat n.toNat
      | throw "percentage must be between 0 and 100."
    return successProbability p
  | _ => unreachable!

end Prio

def parsePrioForUnsafeRule : Option Syntax → Except String Percent
  | none => throw "unsafe rule must be given a success probability."
  | some p => do
    let (Prio.successProbability p) ← Prio.parse p | throw
      "unsafe rule must be given a success probability ('x%'), not an integer penalty"
    return p

def parsePrioForSafeRule : Option Syntax → Except String Int
  | none => return defaultSafePenalty
  | some p => do
    let (Prio.penalty p) ← Prio.parse p | throw
      "safe rule must be given an integer penalty, not a success probability"
    return p

def parsePrioForNormRule : Option Syntax → Except String Int
  | none => return defaultNormPenalty
  | some p => do
    let (Prio.penalty p) ← Prio.parse p | throw
      "norm rule must be given an integer penalty, not a success probability"
    return p

inductive RuleKind
  | norm (penalty : Int)
  | safe (penalty : Int)
  | «unsafe» (successProbability : Percent)
  deriving Inhabited, BEq

namespace RuleKind

instance : ToString RuleKind where
  toString
    | norm p => s!"norm {p}"
    | safe p => s!"safe {p}"
    | «unsafe» p => s!"unsafe {p.toHumanString}"

protected def parse : Syntax → m RuleKind
  | `(aesop_kind|safe $[$prio:aesop_prio]?) =>
    go (parsePrioForSafeRule prio) safe
  | `(aesop_kind|unsafe $[$prio:aesop_prio]?) =>
    go (parsePrioForUnsafeRule prio) «unsafe»
  | `(aesop_kind|$[$prio:aesop_prio]?) =>
    go (parsePrioForUnsafeRule prio) «unsafe»
  | `(aesop_kind|norm $[$prio:aesop_prio]?) =>
    go (parsePrioForNormRule prio) norm
  | _ => unreachable!
  where
    go {α} (prio : Except String α) (cont : α → RuleKind) : m RuleKind :=
      match prio with
      | Except.ok prio => return cont prio
      | Except.error e => throwError "aesop: {e}"

end RuleKind


inductive RegularBuilderClause
  | apply
  | tactic
  | constructors
  | unsafeDefault
  | safeDefault
  deriving Inhabited, BEq

namespace RegularBuilderClause

def builderName : RegularBuilderClause → String
  | apply => "apply"
  | tactic => "tactic"
  | constructors => "constructors"
  | unsafeDefault => "unsafe_default"
  | safeDefault => "safe_default"

instance : ToString RegularBuilderClause where
  toString c := s!"(builder {c.builderName})"

def toRuleBuilder : RegularBuilderClause → RuleBuilder RegularRuleBuilderResult
  | apply => RuleBuilder.apply
  | tactic => RuleBuilder.tactic
  | constructors => RuleBuilder.constructors
  | unsafeDefault => RuleBuilder.unsafeRuleDefault
  | safeDefault => RuleBuilder.safeRuleDefault

end RegularBuilderClause


inductive BuilderClause
  | regular (c : RegularBuilderClause)
  | simpLemma
  | simpUnfold
  | normDefault
  deriving Inhabited, BEq

namespace BuilderClause

def builderName : BuilderClause → String
  | regular c => c.builderName
  | simpLemma => "simp"
  | simpUnfold => "unfold"
  | normDefault => "norm_default"

instance : ToString BuilderClause where
  toString c := s!"(builder {c.builderName})"

open RegularBuilderClause in
protected def parseBuilder : Syntax → BuilderClause
  | `(aesop_builder|apply) => regular apply
  | `(aesop_builder|tactic) => regular tactic
  | `(aesop_builder|constructors) => regular constructors
  | `(aesop_builder|simp) => simpLemma
  | `(aesop_builder|unfold) => simpUnfold
  | `(aesop_builder|unsafe_default) => regular unsafeDefault
  | `(aesop_builder|safe_default) => regular safeDefault
  | `(aesop_builder|norm_default) => normDefault
  | _ => unreachable!

def toRuleBuilder : BuilderClause → RuleBuilder NormRuleBuilderResult
  | regular c => λ goal i =>
    NormRuleBuilderResult.regular <$> c.toRuleBuilder goal i
  | simpLemma => RuleBuilder.normSimpLemmas
  | simpUnfold => RuleBuilder.normSimpUnfold
  | normDefault => RuleBuilder.normRuleDefault

end BuilderClause


inductive Clause
  | builder (c : BuilderClause)
  deriving Inhabited, BEq

namespace Clause

instance : ToString Clause where
  toString
    | builder c => toString c

protected def parse : Syntax → m Clause
  | `(aesop_clause|(builder $b:aesop_builder)) =>
    builder <$> BuilderClause.parseBuilder b
  | _ => unreachable!

end Clause


structure Clauses where
  builder : Option BuilderClause := none

namespace Clauses

def add (cs : Clauses) : Clause → Clauses
  | Clause.builder b =>
    { cs with builder := cs.builder.mergeRightBiased (some b) }

def ofClauseArray (cs : Array Clause) : Clauses :=
  cs.foldl add {}

end Clauses


structure NormRuleClauses where
  builder : BuilderClause

namespace NormRuleClauses

def ofClauses (cs : Clauses) : NormRuleClauses where
  builder := cs.builder.getD BuilderClause.normDefault

end NormRuleClauses

open NormRuleBuilderResult in
def buildNormRule (penalty : Int) (clauses : NormRuleClauses) (i : RuleIdent) :
    MetaM (Array RuleSetMember) := do
  let results ← clauses.builder.toRuleBuilder i
  match results with
  | regular results =>
    results.mapM λ res => RuleSetMember'.normRule
      { name := `norm ++ res.builderName ++ i.ruleName
        indexingMode := res.indexingMode
        usesBranchState := res.mayUseBranchState
        extra := { penalty := penalty }
        tac := res.tac }
  | simpEntries es =>
    return #[RuleSetMember'.normSimpEntries es]


structure SafeRuleClauses where
  builder : RegularBuilderClause
  deriving Inhabited

namespace SafeRuleClauses

def ofClauses (cs : Clauses) : m SafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (BuilderClause.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilderClause.safeDefault
  return { builder := builder }
  where
    errInvalidBuilder {α} (b : BuilderClause) : m α :=
      throwError "aesop: {b.builderName} builder cannot be used with safe rules"

end SafeRuleClauses

def buildSafeRule (penalty : Option Int) (clauses : SafeRuleClauses)
    (i : RuleIdent) : MetaM (Array RuleSetMember) := do
  let results ← clauses.builder.toRuleBuilder i
  let penalty := penalty.getD 0
  results.mapM λ res => RuleSetMember'.safeRule
    { name := `safe ++ res.builderName ++ i.ruleName
      indexingMode := res.indexingMode,
      usesBranchState := res.mayUseBranchState
      extra := { penalty := penalty, safety := Safety.safe }
        -- TODO support almost_safe rules
      tac := res.tac }


structure UnsafeRuleClauses where
  builder : RegularBuilderClause
  deriving Inhabited

namespace UnsafeRuleClauses

def ofClauses (cs : Clauses) : m UnsafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (BuilderClause.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilderClause.unsafeDefault
  return { builder := builder }
  where
    errInvalidBuilder {α} (b : BuilderClause) : m α :=
      throwError "aesop: {b.builderName} builder cannot be used with unsafe rules"

end UnsafeRuleClauses

def buildUnsafeRule (successProbability : Percent) (clauses : UnsafeRuleClauses)
    (i : RuleIdent) : MetaM (Array RuleSetMember) := do
  let results ← clauses.builder.toRuleBuilder i
  results.mapM λ res => RuleSetMember'.unsafeRule
    { name := `unsafe ++ res.builderName ++ i.ruleName
      indexingMode := res.indexingMode,
      usesBranchState := res.mayUseBranchState
      extra := { successProbability := successProbability },
      tac := res.tac }


inductive RuleConfig
  | norm (penalty : Int) (clauses : NormRuleClauses)
  | safe (penalty : Int) (clauses : SafeRuleClauses)
  | «unsafe» (successProbability : Percent) (clauses : UnsafeRuleClauses)
  deriving Inhabited

namespace RuleConfig

protected def ofKindAndClauses (kind : RuleKind) (clauses : Array Clause) :
    m RuleConfig := do
  let clauses := Clauses.ofClauseArray clauses
  match kind with
  | RuleKind.norm penalty =>
    norm penalty <$> NormRuleClauses.ofClauses clauses
  | RuleKind.safe penalty =>
    safe penalty <$> SafeRuleClauses.ofClauses clauses
  | RuleKind.unsafe successProbability =>
    «unsafe» successProbability <$> UnsafeRuleClauses.ofClauses clauses

protected def parse : Syntax → m RuleConfig
  | `(attr|aesop $kind:aesop_kind $[$clauses:aesop_clause]*) => do
    let kind ← RuleKind.parse kind
    let clauses ← clauses.mapM Clause.parse
    RuleConfig.ofKindAndClauses kind clauses
  | _ => unreachable!

protected def applyToRuleIdent (i : RuleIdent) : RuleConfig →
    MetaM (Array RuleSetMember)
  | norm penalty clauses => buildNormRule penalty clauses i
  | safe penalty clauses => buildSafeRule penalty clauses i
  | «unsafe» successProbability clauses =>
    buildUnsafeRule successProbability clauses i

end RuleConfig

structure AesopAttr where
  ext : ScopedEnvExtension (RuleSetMember' RuleTacDescr) RuleSetMember RuleSet
  impl : AttributeImpl
  deriving Inhabited

initialize attr : AesopAttr ← do
  let ext ← registerScopedEnvExtension {
    name := `aesop
    mkInitial := return {}
    ofOLeanEntry := λ rs r => runMetaMAsImportM r.ofDescr
    toOLeanEntry := λ r => r.toDescr.getD
      (panic! "aesop attribute extension: trying to serialise a rule set member without a description")
    addEntry := λ rs r => rs.add r
  }
  let impl : AttributeImpl := {
    name := `aesop
    descr := "Register a declaration as an Aesop rule."
    add := λ decl stx attrKind => do
      let config ← RuleConfig.parse stx
      let rules ← runMetaMAsCoreM $ config.applyToRuleIdent (RuleIdent.const decl)
      rules.forM λ rule => ext.add rule attrKind
    erase := λ _ =>
      throwError "aesop attribute currently cannot be removed"
  }
  -- Despite the name, this also works for non-builtin attributes.
  registerBuiltinAttribute impl
  pure { ext := ext, impl := impl }

def getAttrRuleSet : CoreM RuleSet := do
  attr.ext.getState (← getEnv)

def getRuleSet : MetaM RuleSet := do
  let defaultSimpLemmas ← getSimpLemmas
  let rs ← getAttrRuleSet
  return { rs with normSimpLemmas := defaultSimpLemmas.merge rs.normSimpLemmas }


namespace Parser.Tactic

declare_syntax_cat aesop_rule

syntax ident (aesop_prio)? (aesop_clause)* : aesop_rule

declare_syntax_cat aesop_tactic_clause

syntax ruleList := "[" aesop_rule,+,? "]"

syntax "(" &"unsafe" ruleList ")" : aesop_tactic_clause
syntax "(" &"safe"   ruleList ")" : aesop_tactic_clause
syntax "(" &"norm"   ruleList ")" : aesop_tactic_clause
syntax "(" &"options" term ")" : aesop_tactic_clause

syntax (name := aesop) &"aesop " (aesop_tactic_clause)* : tactic

end Parser.Tactic

structure AdditionalRule where
  ruleIdent : RuleIdent
  config : RuleConfig
  deriving Inhabited

namespace AdditionalRule

protected def parse (prioParser : Option Syntax → Except String α)
    (ruleKind : α → RuleKind) : Syntax → MetaM AdditionalRule
  | `(aesop_rule|$i:ident $[$prio:aesop_prio]? $clauses:aesop_clause*) => do
    let prio ←
      match prioParser prio with
      | Except.ok p => p
      | Except.error e => throwError "aesop: at rule {i}: {e}"
    let clauses ← clauses.mapM Clause.parse
    let config ← RuleConfig.ofKindAndClauses (ruleKind prio) clauses
    return { ruleIdent := (← RuleIdent.ofName i.getId), config := config }
  | _ => unreachable!

protected def toRuleSetMember (r : AdditionalRule) :
    MetaM (Array RuleSetMember) :=
  r.config.applyToRuleIdent r.ruleIdent

end AdditionalRule

inductive TacticClause
  | additionalRules (rs : Array AdditionalRule)
  | options (opts : Aesop.Options)

namespace TacticClause

def parse : Syntax → TermElabM TacticClause
  | `(aesop_tactic_clause|(unsafe [$rules:aesop_rule,*])) => additionalRules <$>
    (rules : Array Syntax).mapM λ stx =>
      AdditionalRule.parse parsePrioForUnsafeRule RuleKind.unsafe stx
  | `(aesop_tactic_clause|(safe [$rules:aesop_rule,*])) => additionalRules <$>
    (rules : Array Syntax).mapM λ stx =>
      AdditionalRule.parse parsePrioForSafeRule RuleKind.safe stx
  | `(aesop_tactic_clause|(norm [$rules:aesop_rule,*])) => additionalRules <$>
    (rules : Array Syntax).mapM λ stx =>
      AdditionalRule.parse parsePrioForNormRule RuleKind.norm stx
  | `(aesop_tactic_clause|(options $t:term)) => do
    let e ← elabTerm t (some (mkConst ``Aesop.Options))
    return options (← evalOptionsExpr e)
  | _ => unreachable!

end TacticClause


structure TacticConfig where
  additionalRules : Array AdditionalRule := #[]
  options : Aesop.Options := {}
  deriving Inhabited

namespace TacticConfig

def addTacticClause (conf : TacticConfig) : TacticClause → TacticConfig
  | TacticClause.additionalRules rs =>
    { conf with additionalRules := conf.additionalRules ++ rs }
  | TacticClause.options opts =>
    { conf with options := opts }

def ofTacticClauses (clauses : Array TacticClause) : TacticConfig :=
  clauses.foldl (init := {}) addTacticClause

-- NOTE: Must be called in the MVar context of the main goal.
protected def parse : Syntax → TermElabM TacticConfig
  | `(tactic|aesop $[$clauses:aesop_tactic_clause]*) =>
    return ofTacticClauses (← clauses.mapM TacticClause.parse)
  | _ => unreachable!

def additionalRuleSetMembers (c : TacticConfig) : MetaM (Array RuleSetMember) :=
  c.additionalRules.concatMapM (·.toRuleSetMember)

end TacticConfig

end Aesop
