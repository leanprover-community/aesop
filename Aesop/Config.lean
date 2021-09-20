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
  deriving Inhabited, BEq

namespace RegularBuilderClause

instance : ToString RegularBuilderClause where
  toString
    | apply => "(builder apply)"
    | tactic => "(builder tactic)"

def toRuleBuilder : RegularBuilderClause → RuleBuilder RegularRuleBuilderResult
  | apply => RuleBuilder.apply
  | tactic => RuleBuilder.tactic

end RegularBuilderClause


inductive BuilderClause
  | regular (c : RegularBuilderClause)
  | simpLemma
  | simpUnfold
  deriving Inhabited, BEq

namespace BuilderClause

instance : ToString BuilderClause where
  toString
    | regular c => toString c
    | simpLemma => "(builder simp)"
    | simpUnfold => "(builder unfold)"

open RegularBuilderClause in
protected def parseBuilder : Syntax → BuilderClause
  | `(aesop_builder|apply) => regular apply
  | `(aesop_builder|tactic) => regular tactic
  | `(aesop_builder|simp) => simpLemma
  | `(aesop_builder|unfold) => simpUnfold
  | _ => unreachable!

def toRuleBuilder : BuilderClause → RuleBuilder NormRuleBuilderResult
  | regular c => λ goal i =>
    NormRuleBuilderResult.regular <$> c.toRuleBuilder goal i
  | simpLemma => RuleBuilder.normSimpLemmas
  | simpUnfold => RuleBuilder.normSimpUnfold

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


structure NormRuleConfig where
  penalty : Option Int
  builder : Option BuilderClause
  deriving Inhabited, BEq

namespace NormRuleConfig

instance : ToString NormRuleConfig where
  toString conf :=
    " ".joinSep
      [ match conf.penalty with | none => "" | some p => toString p,
        match conf.builder with | none => "" | some b => toString b ]

protected def addClause (conf : NormRuleConfig) :
    Clause → m NormRuleConfig
  | Clause.builder b =>
    if conf.builder.isSome
      then throwError "aesop: duplicate builder clause."
      else pure { conf with builder := b }

protected def addClauses (clauses : Array Clause)
    (conf : NormRuleConfig) : m NormRuleConfig :=
  clauses.foldlM NormRuleConfig.addClause conf

open NormRuleBuilderResult in
protected def applyToRuleIdent (i : RuleIdent) (conf : NormRuleConfig) :
    MetaM (Array RuleSetMember) := do
  let results ←
    match conf.builder with
    | none => RuleBuilder.normRuleDefault i
    | some builderClause => builderClause.toRuleBuilder i
  match results with
  | regular results =>
    let penalty := conf.penalty.getD 1
    results.mapM λ res => RuleSetMember'.normRule
      { name := `norm ++ res.builderName ++ i.ruleName
        indexingMode := res.indexingMode
        usesBranchState := res.mayUseBranchState
        extra := { penalty := penalty }
        tac := res.tac }
  | simpEntries es =>
    return #[RuleSetMember'.normSimpEntries es]

end NormRuleConfig


structure SafeRuleConfig where
  penalty : Option Int
  builder : Option RegularBuilderClause
  deriving Inhabited

namespace SafeRuleConfig

instance : ToString SafeRuleConfig where
  toString conf :=
    " ".joinSep
      [ match conf.penalty with | none => "" | some p => toString p,
        match conf.builder with
          | none => ""
          | some b => toString (BuilderClause.regular b) ]

protected def addClause (conf : SafeRuleConfig) : Clause → m SafeRuleConfig
  | Clause.builder BuilderClause.simpLemma =>
    throwError "aesop: 'simp' builder cannot be used with safe rules."
  | Clause.builder BuilderClause.simpUnfold =>
    throwError "aesop: 'unfold' builder cannot be used with safe rules."
  | Clause.builder (BuilderClause.regular b) =>
    if conf.builder.isSome
      then throwError "aesop: duplicate builder clause."
      else pure { conf with builder := b }

protected def addClauses (clauses : Array Clause) (conf : SafeRuleConfig) :
    m SafeRuleConfig :=
  clauses.foldlM SafeRuleConfig.addClause conf

protected def applyToRuleIdent (i : RuleIdent) (conf : SafeRuleConfig) :
    MetaM (Array RuleSetMember) := do
  let results ←
    match conf.builder with
    | none => RuleBuilder.safeRuleDefault i
    | some builderClause => builderClause.toRuleBuilder i
  let penalty := conf.penalty.getD 0
  results.mapM λ res => RuleSetMember'.safeRule
    { name := `safe ++ res.builderName ++ i.ruleName
      indexingMode := res.indexingMode,
      usesBranchState := res.mayUseBranchState
      extra := { penalty := penalty, safety := Safety.safe }
        -- TODO support almost_safe rules
      tac := res.tac }

end SafeRuleConfig


structure UnsafeRuleConfig where
  successProbability : Percent
  builder : Option RegularBuilderClause
  deriving Inhabited

namespace UnsafeRuleConfig

instance : ToString UnsafeRuleConfig where
  toString conf :=
    " ".joinSep
      [ conf.successProbability.toHumanString,
        match conf.builder with
          | none => ""
          | some b => toString (BuilderClause.regular b) ]

protected def addClause (conf : UnsafeRuleConfig) : Clause → m UnsafeRuleConfig
  | Clause.builder BuilderClause.simpLemma =>
    throwError "aesop: 'simp' builder cannot be used with unsafe rules."
  | Clause.builder BuilderClause.simpUnfold =>
    throwError "aesop: 'unfold' builder cannot be used with unsafe rules."
  | Clause.builder (BuilderClause.regular b) =>
    if conf.builder.isSome
      then throwError "aesop: duplicate builder clause."
      else pure { conf with builder := b }

protected def addClauses (clauses : Array Clause) (conf : UnsafeRuleConfig) :
    m UnsafeRuleConfig :=
  clauses.foldlM UnsafeRuleConfig.addClause conf

protected def applyToRuleIdent (i : RuleIdent) (conf : UnsafeRuleConfig) :
    MetaM (Array RuleSetMember) := do
  let results ←
    match conf.builder with
    | none => RuleBuilder.unsafeRuleDefault i
    | some builderClause => builderClause.toRuleBuilder i
  results.mapM λ res => RuleSetMember'.unsafeRule
    { name := `unsafe ++ res.builderName ++ i.ruleName
      indexingMode := res.indexingMode,
      usesBranchState := res.mayUseBranchState
      extra := { successProbability := conf.successProbability },
      tac := res.tac }

end UnsafeRuleConfig


inductive RuleConfig
  | norm (conf : NormRuleConfig)
  | safe (conf : SafeRuleConfig)
  | «unsafe» (conf : UnsafeRuleConfig)
  deriving Inhabited

namespace RuleConfig

instance : ToString RuleConfig where
  toString c :=
    "aesop " ++
    match c with
      | norm conf => " ".joinSep ["norm", toString conf]
      | safe conf => " ".joinSep ["safe", toString conf]
      | «unsafe» conf => " ".joinSep ["unsafe", toString conf]

protected def ofKindAndClauses : RuleKind → Array Clause → m RuleConfig
  | RuleKind.norm penalty, cs => do
    let conf : NormRuleConfig := { penalty := penalty, builder := none }
    norm <$> conf.addClauses cs
  | RuleKind.safe penalty, cs => do
    let conf : SafeRuleConfig := { penalty := penalty, builder := none }
    safe <$> conf.addClauses cs
  | RuleKind.unsafe prob, cs => do
    let conf : UnsafeRuleConfig := { successProbability := prob, builder := none }
    «unsafe» <$> conf.addClauses cs

protected def parse : Syntax → m RuleConfig
  | `(attr|aesop $kind:aesop_kind $[$clauses:aesop_clause]*) => do
    let kind ← RuleKind.parse kind
    let clauses ← clauses.mapM Clause.parse
    RuleConfig.ofKindAndClauses kind clauses
  | _ => unreachable!

protected def applyToRuleIdent (i : RuleIdent) :
    RuleConfig → MetaM (Array RuleSetMember)
  | norm conf => conf.applyToRuleIdent i
  | safe conf => conf.applyToRuleIdent i
  | «unsafe» conf => conf.applyToRuleIdent i

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
