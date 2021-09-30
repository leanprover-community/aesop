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
open Std (HashSet)

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

declare_syntax_cat' aesop_builder_clause force_leading_unreserved_tokens

syntax &"uses_branch_state" : aesop_builder_clause
syntax &"uses_no_branch_state" : aesop_builder_clause

declare_syntax_cat' aesop_clause

syntax "(" &"builder" aesop_builder aesop_builder_clause* ")" : aesop_clause
syntax "(" &"options" term ")" : aesop_clause

syntax (name := aesop) &"aesop" aesop_kind aesop_clause* : attr

end Parser.Attribute


namespace Config

variable [Monad m] [MonadError m]


inductive Prio
  | successProbability (p : Percent)
  | penalty (i : Int)
  deriving Inhabited

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
  deriving Inhabited

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
      ofExcept $ prio.map cont |>.mapError λ e => "aesop : {e}"

end RuleKind


inductive BuilderOption
  | usesBranchState
  | usesNoBranchState
  deriving Inhabited

namespace BuilderOption

instance : ToString BuilderOption where
  toString
    | usesBranchState => "uses_branch_state"
    | usesNoBranchState => "uses_no_branch_state"

protected def parse : Syntax → BuilderOption
  | `(aesop_builder_clause|uses_branch_state) => usesBranchState
  | `(aesop_builder_clause|uses_no_branch_state) => usesNoBranchState
  | _ => unreachable!

protected def parseMany (stxs : Array Syntax) : Array BuilderOption :=
  stxs.map BuilderOption.parse

end BuilderOption


structure BuilderOptions where
  usesBranchState : Option Bool := none
  deriving Inhabited

namespace BuilderOptions

protected def add (opts : BuilderOptions) :  BuilderOption → BuilderOptions
  | BuilderOption.usesBranchState =>
    { opts with
      usesBranchState := opts.usesBranchState.mergeRightBiased (some True) }
  | BuilderOption.usesNoBranchState =>
    { opts with
      usesBranchState := opts.usesBranchState.mergeRightBiased (some False) }

def ofBuilderOptionArray (opts : Array BuilderOption) : BuilderOptions :=
  opts.foldl BuilderOptions.add {}

-- NOTE: Make sure this set contains every field of `BuilderOptions`.
def definedFields : BuilderOptions → HashSet Name
  | { usesBranchState } =>
    HashSet.empty
    |> go usesBranchState `usesBranchState
  where
    go {α} (o : Option α) (n : Name) (ns : HashSet Name) : HashSet Name :=
      match o with
      | none => ns
      | some _ => ns.insert n

def parse (stxs : Array Syntax) : BuilderOptions :=
  ofBuilderOptionArray $ stxs.map BuilderOption.parse

end BuilderOptions


private def checkBuilderOptionsContainOnly (builderName : String)
    (possibleOptions : Array Name) (opts : BuilderOptions) : m Unit := do
  let mut defined := opts.definedFields
  for n in possibleOptions do
    defined := defined.erase n
  unless defined.isEmpty do
    let extraOpts := MessageData.joinSep (defined.toList.map toMessageData) ", "
    throwError "aesop: builder {builderName} does not support these options: {extraOpts}"

private def checkNoBuilderOptions (builderName : String)
    (opts : BuilderOptions) : m Unit :=
  checkBuilderOptionsContainOnly builderName #[] opts

def tacticBuilderOptionsOfBuilderOptions (opts : BuilderOptions) :
    m TacticBuilderOptions := do
  checkBuilderOptionsContainOnly "tactic" #[`usesBranchState] opts
  return { usesBranchState := opts.usesBranchState.getD true }

def tacticBuilderOptionsToBuilderOptions (opts : TacticBuilderOptions) :
    BuilderOptions :=
  { usesBranchState := opts.usesBranchState }

inductive RegularBuilder
  | apply
  | tactic (opts : TacticBuilderOptions)
  | constructors
  | unsafeDefault
  | safeDefault
  deriving Inhabited

namespace RegularBuilder

protected def name : RegularBuilder → String
  | apply => "apply"
  | tactic .. => "tactic"
  | constructors => "constructors"
  | unsafeDefault => "unsafe_default"
  | safeDefault => "safe_default"

def toGlobalRuleBuilder : RegularBuilder → GlobalRuleBuilder RegularRuleBuilderResult
  | apply => GlobalRuleBuilder.apply
  | tactic opts => GlobalRuleBuilder.tactic opts
  | constructors => GlobalRuleBuilder.constructors
  | unsafeDefault => GlobalRuleBuilder.unsafeRuleDefault
  | safeDefault => GlobalRuleBuilder.safeRuleDefault

def toRuleBuilder : RegularBuilder → RuleBuilder RegularRuleBuilderResult
  | apply => RuleBuilder.apply
  | tactic opts => RuleBuilder.tactic opts
  | constructors => RuleBuilder.constructors
  | unsafeDefault => RuleBuilder.unsafeRuleDefault
  | safeDefault => RuleBuilder.safeRuleDefault

end RegularBuilder


inductive Builder
  | regular (c : RegularBuilder)
  | simpLemma
  | simpUnfold
  | normDefault
  deriving Inhabited

namespace Builder

protected def name : Builder → String
  | regular c => c.name
  | simpLemma => "simp"
  | simpUnfold => "unfold"
  | normDefault => "norm_default"

open RegularBuilder in
protected def parse (builder : Syntax) (clauses : Array Syntax) : m Builder := do
  let opts := BuilderOptions.parse clauses
  match builder with
  | `(aesop_builder|apply) => do
    checkNoBuilderOptions apply.name opts
    return regular apply
  | `(aesop_builder|tactic) => do
    let opts ← tacticBuilderOptionsOfBuilderOptions opts
    return regular $ tactic opts
  | `(aesop_builder|constructors) => do
    checkNoBuilderOptions constructors.name opts
    return regular constructors
  | `(aesop_builder|simp) => do
    checkNoBuilderOptions simpLemma.name opts
    return simpLemma
  | `(aesop_builder|unfold) => do
    checkNoBuilderOptions simpUnfold.name opts
    return simpUnfold
  | `(aesop_builder|unsafe_default) => do
    checkNoBuilderOptions unsafeDefault.name opts
    return regular unsafeDefault
  | `(aesop_builder|safe_default) => do
    checkNoBuilderOptions safeDefault.name opts
    return regular safeDefault
  | `(aesop_builder|norm_default) => do
    checkNoBuilderOptions normDefault.name opts
    return normDefault
  | _ => unreachable!

def toRuleBuilder : Builder → RuleBuilder NormRuleBuilderResult
  | regular c => λ id goal => do
    let (goal, result) ← c.toRuleBuilder id goal
    return (goal, NormRuleBuilderResult.regular result)
  | simpLemma => RuleBuilder.normSimpLemmas
  | simpUnfold => RuleBuilder.normSimpUnfold
  | normDefault => RuleBuilder.normRuleDefault

def toGlobalRuleBuilder : Builder → GlobalRuleBuilder NormRuleBuilderResult
  | regular c => λ decl =>
    NormRuleBuilderResult.regular <$> c.toGlobalRuleBuilder decl
  | simpLemma => GlobalRuleBuilder.normSimpLemmas
  | simpUnfold => GlobalRuleBuilder.normSimpUnfold
  | normDefault => GlobalRuleBuilder.normRuleDefault

end Builder


inductive Clause
  | builder (c : Builder)
  deriving Inhabited

namespace Clause

protected def parse : Syntax → m Clause
  | `(aesop_clause|(builder $b:aesop_builder $cs:aesop_builder_clause*)) =>
    builder <$> Builder.parse b cs
  | _ => unreachable!

end Clause


structure Clauses where
  builder : Option Builder := none

namespace Clauses

def add (cs : Clauses) : Clause → Clauses
  | Clause.builder b =>
    { cs with builder := cs.builder.mergeRightBiased (some b) }

def ofClauseArray (cs : Array Clause) : Clauses :=
  cs.foldl add {}

end Clauses


structure NormRuleClauses where
  builder : Builder

namespace NormRuleClauses

def ofClauses (cs : Clauses) : NormRuleClauses where
  builder := cs.builder.getD Builder.normDefault

end NormRuleClauses

private def normRuleBuilderResultToRuleSetMembers (penalty : Int)
    (id : RuleIdent) : NormRuleBuilderResult → Array RuleSetMember
  | NormRuleBuilderResult.regular results =>
    results.map λ res => RuleSetMember'.normRule {
      name := `norm ++ res.builderName ++ id.ruleName
      indexingMode := res.indexingMode
      usesBranchState := res.mayUseBranchState
      extra := { penalty := penalty }
      tac := res.tac
    }
  | NormRuleBuilderResult.simpEntries entries =>
    #[RuleSetMember'.normSimpEntries entries]

def buildGlobalNormRule (penalty : Int) (clauses : NormRuleClauses)
    (decl : Name) : MetaM (Array RuleSetMember) :=
  normRuleBuilderResultToRuleSetMembers penalty (RuleIdent.const decl) <$>
    clauses.builder.toGlobalRuleBuilder decl

def buildLocalNormRule (goal : MVarId) (penalty : Int)
    (clauses : NormRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × Array RuleSetMember) := do
  let (goal, res) ← clauses.builder.toRuleBuilder id goal
  return (goal, normRuleBuilderResultToRuleSetMembers penalty id res)


structure SafeRuleClauses where
  builder : RegularBuilder
  deriving Inhabited

namespace SafeRuleClauses

def ofClauses (cs : Clauses) : m SafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (Builder.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilder.safeDefault
  return { builder := builder }
  where
    errInvalidBuilder {α} (b : Builder) : m α :=
      throwError "aesop: {b.name} builder cannot be used with safe rules"

end SafeRuleClauses

private def safeRuleBuilderResultToRuleSetMembers (id : RuleIdent)
    (penalty : Option Int) (r : RegularRuleBuilderResult) :
    Array RuleSetMember :=
  r.map λ res => RuleSetMember'.safeRule {
    name := `safe ++ res.builderName ++ id.ruleName
    indexingMode := res.indexingMode,
    usesBranchState := res.mayUseBranchState
    extra := { penalty := penalty.getD 0, safety := Safety.safe }
      -- TODO support almost_safe rules
    tac := res.tac
  }

def buildGlobalSafeRule (penalty : Option Int) (clauses : SafeRuleClauses)
    (id : Name) : MetaM (Array RuleSetMember) :=
  safeRuleBuilderResultToRuleSetMembers (RuleIdent.const id) penalty <$>
    clauses.builder.toGlobalRuleBuilder id

def buildLocalSafeRule (goal : MVarId) (penalty : Option Int)
    (clauses : SafeRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × Array RuleSetMember) := do
  let (goal, res) ← clauses.builder.toRuleBuilder id goal
  return (goal, safeRuleBuilderResultToRuleSetMembers id penalty res)


structure UnsafeRuleClauses where
  builder : RegularBuilder
  deriving Inhabited

namespace UnsafeRuleClauses

def ofClauses (cs : Clauses) : m UnsafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (Builder.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilder.unsafeDefault
  return { builder := builder }
  where
    errInvalidBuilder {α} (b : Builder) : m α :=
      throwError "aesop: {b.name} builder cannot be used with unsafe rules"

end UnsafeRuleClauses

private def unsafeRuleBuilderResultToRuleSetMembers
    (successProbability : Percent) (id : RuleIdent)
    (r : RegularRuleBuilderResult) :
    Array RuleSetMember :=
  r.map λ res => RuleSetMember'.unsafeRule {
    name := `unsafe ++ res.builderName ++ id.ruleName
    indexingMode := res.indexingMode,
    usesBranchState := res.mayUseBranchState
    extra := { successProbability := successProbability },
    tac := res.tac
  }

def buildGlobalUnsafeRule (successProbability : Percent)
    (clauses : UnsafeRuleClauses) (id : Name) :
    MetaM (Array RuleSetMember) := do
  let res ← clauses.builder.toGlobalRuleBuilder id
  unsafeRuleBuilderResultToRuleSetMembers successProbability
    (RuleIdent.const id) res

def buildLocalUnsafeRule (goal : MVarId) (successProbability : Percent)
    (clauses : UnsafeRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × Array RuleSetMember) := do
  let (goal, results) ← clauses.builder.toRuleBuilder id goal
  let results :=
    unsafeRuleBuilderResultToRuleSetMembers successProbability id results
  return (goal, results)

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

protected def buildGlobalRule (id : Name) : RuleConfig →
    MetaM (Array RuleSetMember)
  | norm penalty clauses => buildGlobalNormRule penalty clauses id
  | safe penalty clauses => buildGlobalSafeRule penalty clauses id
  | «unsafe» successProbability clauses =>
    buildGlobalUnsafeRule successProbability clauses id

protected def buildLocalRule (goal : MVarId) (id : RuleIdent) :
    RuleConfig → MetaM (MVarId × Array RuleSetMember)
  | norm penalty clauses => buildLocalNormRule goal penalty clauses id
  | safe penalty clauses => buildLocalSafeRule goal penalty clauses id
  | «unsafe» successProbability clauses =>
    buildLocalUnsafeRule goal successProbability clauses id

end RuleConfig

structure AesopAttr where
  ext : ScopedEnvExtension RuleSetMemberDescr RuleSetMember RuleSet
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
      let rules ← runMetaMAsCoreM $ config.buildGlobalRule decl
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

end Config


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


namespace Config

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

protected def build (goal : MVarId) (r : AdditionalRule) :
    MetaM (MVarId × Array RuleSetMember) :=
  r.config.buildLocalRule goal r.ruleIdent

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

def buildAdditionalRules (goal : MVarId) (c : TacticConfig) :
    MetaM (MVarId × Array RuleSetMember) := do
  let mut goal := goal
  let mut rules := #[]
  for r in c.additionalRules do
    let (goal', rules') ← r.build goal
    goal := goal'
    rules := rules ++ rules'
  return (goal, rules)

end TacticConfig

end Aesop.Config
