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

namespace Parser.Command

syntax (name := declareAesopRuleSets) "declare_aesop_rule_sets" "[" ident,+,? "]" : command

end Command


namespace Attribute

declare_syntax_cat aesop_prio

syntax "-"? num "%"? : aesop_prio

declare_syntax_cat aesop_kind (behavior := symbol)

syntax (aesop_prio)? : aesop_kind
syntax &"safe" (aesop_prio)? : aesop_kind
syntax &"unsafe" (aesop_prio)? : aesop_kind
syntax &"norm" (aesop_prio)? : aesop_kind

declare_syntax_cat aesop_builder (behavior := symbol)

syntax &"apply" : aesop_builder
syntax &"simp" : aesop_builder
syntax &"unfold" : aesop_builder
syntax &"tactic" : aesop_builder
syntax &"constructors" : aesop_builder
syntax &"forward" : aesop_builder
syntax &"cases" : aesop_builder
syntax &"safe_default" : aesop_builder
syntax &"unsafe_default" : aesop_builder
syntax &"norm_default" : aesop_builder

declare_syntax_cat aesop_builder_clause (behavior := symbol)

syntax &"uses_branch_state" : aesop_builder_clause
syntax &"uses_no_branch_state" : aesop_builder_clause
syntax "(" &"immediate" ident+ ")" : aesop_builder_clause

declare_syntax_cat aesop_clause (behavior := symbol)

syntax "(" &"builder" aesop_builder aesop_builder_clause* ")" : aesop_clause
syntax "(" &"options" term ")" : aesop_clause
syntax "(" &"rulesets" "[" ident,+,? "]" ")" : aesop_clause

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
      ofExcept $ prio.map cont |>.mapError λ e => s!"aesop : {e}"

end RuleKind


inductive BuilderOption
  | usesBranchState
  | usesNoBranchState
  | forwardImmediate (names : Array Name)
  deriving Inhabited

namespace BuilderOption

instance : ToString BuilderOption where
  toString
    | usesBranchState => "uses_branch_state"
    | usesNoBranchState => "uses_no_branch_state"
    | forwardImmediate names => s!"(immediate {names})"

protected def parse : Syntax → BuilderOption
  | `(aesop_builder_clause|uses_branch_state) => usesBranchState
  | `(aesop_builder_clause|uses_no_branch_state) => usesNoBranchState
  | `(aesop_builder_clause|(immediate $ids:ident*)) => forwardImmediate $
    ids.map (·.getId)
  | _ => unreachable!

protected def parseMany (stxs : Array Syntax) : Array BuilderOption :=
  stxs.map BuilderOption.parse

end BuilderOption


structure BuilderOptions where
  usesBranchState : Option Bool := none
  forwardImmediate : Option (Array Name) := none
  deriving Inhabited

namespace BuilderOptions

private def mergeArrays : Option (Array α) → Array α → Option (Array α)
  | none, ys => some ys
  | some xs, ys => some $ xs ++ ys

protected def add (opts : BuilderOptions) :  BuilderOption → BuilderOptions
  | BuilderOption.usesBranchState =>
    { opts with
      usesBranchState := opts.usesBranchState.mergeRightBiased (some True) }
  | BuilderOption.usesNoBranchState =>
    { opts with
      usesBranchState := opts.usesBranchState.mergeRightBiased (some False) }
  | BuilderOption.forwardImmediate names =>
    { opts with
      forwardImmediate := mergeArrays opts.forwardImmediate names }

def ofBuilderOptionArray (opts : Array BuilderOption) : BuilderOptions :=
  opts.foldl BuilderOptions.add {}

-- NOTE: Make sure this set contains every field of `BuilderOptions`.
def definedFields : BuilderOptions → HashSet Name
  | { usesBranchState, forwardImmediate } =>
    HashSet.empty
    |> go usesBranchState `usesBranchState
    |> go forwardImmediate `forwardImmediate
  where
    go {α} (o : Option α) (n : Name) (ns : HashSet Name) : HashSet Name :=
      match o with
      | none => ns
      | some _ => ns.insert n

def parse (stxs : Array Syntax) : BuilderOptions :=
  ofBuilderOptionArray $ stxs.map BuilderOption.parse

end BuilderOptions


private def checkBuilderOptionsContainOnly (builderName : RuleName.Builder)
    (possibleOptions : Array Name) (opts : BuilderOptions) : m Unit := do
  let mut defined := opts.definedFields
  for n in possibleOptions do
    defined := defined.erase n
  unless defined.isEmpty do
    let extraOpts := MessageData.joinSep (defined.toList.map toMessageData) ", "
    throwError "aesop: builder {builderName} does not support these options: {extraOpts}"

private def checkNoBuilderOptions (builderName : RuleName.Builder)
    (opts : BuilderOptions) : m Unit :=
  checkBuilderOptionsContainOnly builderName #[] opts

def tacticBuilderOptionsOfBuilderOptions (opts : BuilderOptions) :
    m TacticBuilderOptions := do
  checkBuilderOptionsContainOnly RuleName.Builder.tactic #[`usesBranchState] opts
  return { usesBranchState := opts.usesBranchState.getD true }

def tacticBuilderOptionsToBuilderOptions (opts : TacticBuilderOptions) :
    BuilderOptions :=
  { usesBranchState := some opts.usesBranchState }

def forwardBuilderOptionsOfBuilderOptions (opts : BuilderOptions) :
    m ForwardBuilderOptions := do
  checkBuilderOptionsContainOnly RuleName.Builder.forward
    #[`forwardImmediate] opts
  return { immediateHyps := opts.forwardImmediate.getD #[] }

def forwardBuilderOptionsToBuilderOptions (opts : ForwardBuilderOptions) :
    BuilderOptions :=
  { forwardImmediate := some opts.immediateHyps }

inductive RegularBuilder
  | apply
  | tactic (opts : TacticBuilderOptions)
  | constructors
  | cases
  | forward (opts : ForwardBuilderOptions)
  | unsafeDefault
  | safeDefault
  deriving Inhabited

namespace RegularBuilder

def name : RegularBuilder → RuleName.Builder
  | apply => RuleName.Builder.apply
  | tactic .. => RuleName.Builder.tactic
  | constructors => RuleName.Builder.constructors
  | cases => RuleName.Builder.cases
  | forward .. => RuleName.Builder.forward
  | unsafeDefault => RuleName.Builder.unsafeDefault
  | safeDefault => RuleName.Builder.safeDefault

def toGlobalRuleBuilder : RegularBuilder → GlobalRuleBuilder RegularRuleBuilderResult
  | apply => GlobalRuleBuilder.apply
  | forward opts => GlobalRuleBuilder.forward opts
  | tactic opts => GlobalRuleBuilder.tactic opts
  | constructors => GlobalRuleBuilder.constructors
  | cases => GlobalRuleBuilder.cases
  | unsafeDefault => GlobalRuleBuilder.unsafeRuleDefault
  | safeDefault => GlobalRuleBuilder.safeRuleDefault

def toRuleBuilder : RegularBuilder → RuleBuilder RegularRuleBuilderResult
  | apply => RuleBuilder.apply
  | tactic opts => RuleBuilder.tactic opts
  | constructors => RuleBuilder.constructors
  | cases => RuleBuilder.cases
  | forward opts => RuleBuilder.forward opts
  | unsafeDefault => RuleBuilder.unsafeRuleDefault
  | safeDefault => RuleBuilder.safeRuleDefault

end RegularBuilder


inductive Builder
  | regular (c : RegularBuilder)
  | simp
  | unfold
  | normDefault
  deriving Inhabited

namespace Builder

def name : Builder → RuleName.Builder
  | regular c => c.name
  | simp => RuleName.Builder.simp
  | unfold => RuleName.Builder.unfold
  | normDefault => RuleName.Builder.normDefault

open RegularBuilder in
protected def parse (builder : Syntax) (clauses : Array Syntax) : m Builder := do
  let opts := BuilderOptions.parse clauses
  match builder with
  | `(aesop_builder|apply) => do
    checkNoBuilderOptions RuleName.Builder.apply opts
    return regular apply
  | `(aesop_builder|tactic) => do
    let opts ← tacticBuilderOptionsOfBuilderOptions opts
    return regular $ tactic opts
  | `(aesop_builder|constructors) => do
    checkNoBuilderOptions RuleName.Builder.constructors opts
    return regular constructors
  | `(aesop_builder|cases) => do
    checkNoBuilderOptions RuleName.Builder.cases opts
    return regular cases
  | `(aesop_builder|forward) => do
    let opts ← forwardBuilderOptionsOfBuilderOptions opts
    return regular $ forward opts
  | `(aesop_builder|simp) => do
    checkNoBuilderOptions RuleName.Builder.simp opts
    return simp
  | `(aesop_builder|unfold) => do
    checkNoBuilderOptions RuleName.Builder.unfold opts
    return unfold
  | `(aesop_builder|unsafe_default) => do
    checkNoBuilderOptions RuleName.Builder.unsafeDefault opts
    return regular unsafeDefault
  | `(aesop_builder|safe_default) => do
    checkNoBuilderOptions RuleName.Builder.safeDefault opts
    return regular safeDefault
  | `(aesop_builder|norm_default) => do
    checkNoBuilderOptions RuleName.Builder.normDefault opts
    return normDefault
  | _ => unreachable!

def toRuleBuilder : Builder → RuleBuilder NormRuleBuilderResult
  | regular c => λ id goal => do
    let (goal, result) ← c.toRuleBuilder id goal
    return (goal, NormRuleBuilderResult.regular result)
  | simp => RuleBuilder.normSimpLemmas
  | unfold => RuleBuilder.normSimpUnfold
  | normDefault => RuleBuilder.normRuleDefault

def toGlobalRuleBuilder : Builder → GlobalRuleBuilder NormRuleBuilderResult
  | regular c => λ decl =>
    NormRuleBuilderResult.regular <$> c.toGlobalRuleBuilder decl
  | simp => GlobalRuleBuilder.normSimpLemmas
  | unfold => GlobalRuleBuilder.normSimpUnfold
  | normDefault => GlobalRuleBuilder.normRuleDefault

end Builder


inductive Clause
  | builder (c : Builder)
  | ruleSets (rss : Array RuleSetName)
  deriving Inhabited

namespace Clause

protected def parse (isLocalRule : Bool) : Syntax → m Clause
  | `(aesop_clause|(builder $b:aesop_builder $cs:aesop_builder_clause*)) =>
    builder <$> Builder.parse b cs
  | `(aesop_clause|(rulesets [ $rss:ident,* ])) => do
    if isLocalRule then
      throwError "aesop: 'rulesets' clause not allowed for local rules"
    ruleSets $ (rss : Array Syntax).map (·.getId)
  | _ => unreachable!

end Clause


structure Clauses where
  builder : Option Builder := none
  ruleSets : Option (Array RuleSetName) := none

namespace Clauses

def add (cs : Clauses) : Clause → Clauses
  | Clause.builder b =>
    { cs with builder := cs.builder.mergeRightBiased (some b) }
  | Clause.ruleSets newRss =>
    let rss :=
      match cs.ruleSets with
      | none => newRss
      | some oldRss =>
        newRss.foldl (init := oldRss) λ rss rsName =>
          if rss.contains rsName then rss else rss.push rsName
    { cs with ruleSets := some rss }

def ofClauseArray (cs : Array Clause) : Clauses :=
  cs.foldl add {}

def ruleSets' (cs : Clauses) : Array RuleSetName :=
  cs.ruleSets.getD #[defaultRuleSetName]

end Clauses


structure NormRuleClauses where
  builder : Builder
  ruleSets : Array RuleSetName
  deriving Inhabited

namespace NormRuleClauses

def ofClauses (cs : Clauses) : NormRuleClauses where
  builder := cs.builder.getD Builder.normDefault
  ruleSets := cs.ruleSets'

end NormRuleClauses

private def normRuleBuilderResultToRuleSetMember (penalty : Int)
    (id : RuleIdent) : NormRuleBuilderResult → RuleSetMember
  | NormRuleBuilderResult.regular res =>
    RuleSetMember'.normRule {
      name := id.toRuleName RuleName.Phase.norm res.builder
      indexingMode := res.indexingMode
      usesBranchState := res.mayUseBranchState
      extra := { penalty := penalty }
      tac := res.tac
    }
  | NormRuleBuilderResult.simp res =>
    RuleSetMember'.normSimpRule {
      name := id.toRuleName RuleName.Phase.norm res.builder
      entries := res.entries
    }

def buildGlobalNormRule (penalty : Int) (clauses : NormRuleClauses)
    (decl : Name) : MetaM RuleSetMember := do
  normRuleBuilderResultToRuleSetMember penalty (RuleIdent.const decl) <$>
    clauses.builder.toGlobalRuleBuilder decl

def buildLocalNormRule (goal : MVarId) (penalty : Int)
    (clauses : NormRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × RuleSetMember) := do
  let (goal, res) ← clauses.builder.toRuleBuilder id goal
  return (goal, normRuleBuilderResultToRuleSetMember penalty id res)


structure SafeRuleClauses where
  builder : RegularBuilder
  ruleSets : Array RuleSetName
  deriving Inhabited

namespace SafeRuleClauses

def ofClauses (cs : Clauses) : m SafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (Builder.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilder.safeDefault
  return {
    builder := builder
    ruleSets := cs.ruleSets'
  }
  where
    errInvalidBuilder {α} (b : Builder) : m α :=
      throwError "aesop: {b.name} builder cannot be used with safe rules"

end SafeRuleClauses

private def safeRuleBuilderResultToRuleSetMember (id : RuleIdent)
    (penalty : Option Int) (r : RegularRuleBuilderResult) :
    RuleSetMember :=
  RuleSetMember'.safeRule {
    name := id.toRuleName RuleName.Phase.safe r.builder
    indexingMode := r.indexingMode,
    usesBranchState := r.mayUseBranchState
    extra := { penalty := penalty.getD 0, safety := Safety.safe }
      -- TODO support almost_safe rules
    tac := r.tac
  }

def buildGlobalSafeRule (penalty : Option Int) (clauses : SafeRuleClauses)
    (id : Name) : MetaM RuleSetMember :=
  safeRuleBuilderResultToRuleSetMember (RuleIdent.const id) penalty <$>
    clauses.builder.toGlobalRuleBuilder id

def buildLocalSafeRule (goal : MVarId) (penalty : Option Int)
    (clauses : SafeRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × RuleSetMember) := do
  let (goal, res) ← clauses.builder.toRuleBuilder id goal
  return (goal, safeRuleBuilderResultToRuleSetMember id penalty res)


structure UnsafeRuleClauses where
  builder : RegularBuilder
  ruleSets : Array RuleSetName
  deriving Inhabited

namespace UnsafeRuleClauses

def ofClauses (cs : Clauses) : m UnsafeRuleClauses := do
  let builder ←
    match cs.builder with
    | some (Builder.regular b) => pure b
    | some b => errInvalidBuilder b
    | none => pure RegularBuilder.unsafeDefault
  return {
    builder := builder
    ruleSets := cs.ruleSets'
  }
  where
    errInvalidBuilder {α} (b : Builder) : m α :=
      throwError "aesop: {b.name} builder cannot be used with unsafe rules"

end UnsafeRuleClauses

private def unsafeRuleBuilderResultToRuleSetMember
    (successProbability : Percent) (id : RuleIdent)
    (r : RegularRuleBuilderResult) :
    RuleSetMember :=
  RuleSetMember'.unsafeRule {
    name := id.toRuleName RuleName.Phase.unsafe r.builder
    indexingMode := r.indexingMode,
    usesBranchState := r.mayUseBranchState
    extra := { successProbability := successProbability },
    tac := r.tac
  }

def buildGlobalUnsafeRule (successProbability : Percent)
    (clauses : UnsafeRuleClauses) (id : Name) :
    MetaM RuleSetMember := do
  let res ← clauses.builder.toGlobalRuleBuilder id
  unsafeRuleBuilderResultToRuleSetMember successProbability
    (RuleIdent.const id) res

def buildLocalUnsafeRule (goal : MVarId) (successProbability : Percent)
    (clauses : UnsafeRuleClauses) (id : RuleIdent) :
    MetaM (MVarId × RuleSetMember) := do
  let (goal, results) ← clauses.builder.toRuleBuilder id goal
  let results :=
    unsafeRuleBuilderResultToRuleSetMember successProbability id results
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

protected def parse (isLocalRule : Bool) : Syntax → m RuleConfig
  | `(attr|aesop $kind:aesop_kind $[$clauses:aesop_clause]*) => do
    let kind ← RuleKind.parse kind
    let clauses ← clauses.mapM (Clause.parse isLocalRule)
    RuleConfig.ofKindAndClauses kind clauses
  | _ => unreachable!

protected def buildGlobalRule (id : Name) : RuleConfig →
    MetaM RuleSetMember
  | norm penalty clauses => buildGlobalNormRule penalty clauses id
  | safe penalty clauses => buildGlobalSafeRule penalty clauses id
  | «unsafe» successProbability clauses =>
    buildGlobalUnsafeRule successProbability clauses id

protected def buildLocalRule (goal : MVarId) (id : RuleIdent) :
    RuleConfig → MetaM (MVarId × RuleSetMember)
  | norm penalty clauses => buildLocalNormRule goal penalty clauses id
  | safe penalty clauses => buildLocalSafeRule goal penalty clauses id
  | «unsafe» successProbability clauses =>
    buildLocalUnsafeRule goal successProbability clauses id

protected def ruleSets : RuleConfig → Array RuleSetName
  | norm _ clauses => clauses.ruleSets
  | safe _ clauses => clauses.ruleSets
  | «unsafe» _ clauses => clauses.ruleSets

end RuleConfig


initialize extension :
    PersistentEnvExtension
      (RuleSetName × RuleSetMemberDescr)
      (RuleSetName × RuleSetMember)
      RuleSets ← do
  let ext ← registerPersistentEnvExtension {
    name := `aesop
    mkInitial := return {}
    addImportedFn := λ rss => do
      let mut result := {}
      for rs in rss do
        for (rsName, rDescr) in rs do
          result := result.addRule rsName (← runMetaMAsImportM rDescr.ofDescr)
      return result
    addEntryFn := λ rss (rsName, r) => rss.addRule rsName r
    exportEntriesFn := λ rss => rss.toDescrArray!
  }
  let impl : AttributeImpl := {
    name := `aesop
    descr := "Register a declaration as an Aesop rule."
    add := λ decl stx attrKind => do
      -- TODO error on attrKind = local or attrKind = scoped
      let config ← RuleConfig.parse (isLocalRule := false) stx
      let rule ← runMetaMAsCoreM $ config.buildGlobalRule decl
      let ruleSets := config.ruleSets
      let mut rss := ext.getState (← getEnv)
      for rsName in ruleSets do
        if ! rss.containsRuleSet rsName then
          throwError "aesop: no such rule set: '{rsName}'\n  (Use 'declare_aesop_rule_set' to declare rule sets.)"
        if rss.containsRule rsName rule.name then
          throwError "aesop: '{rule.name.name}' is already registered in rule set '{rsName}'."
        rss := rss.addRule rsName rule
      setEnv $ ext.setState (← getEnv) rss
    erase := λ decl => do
      let rss := ext.getState (← getEnv)
      let (rss, erased) := rss.eraseAllRulesWithIdent $ RuleIdent.const decl
      unless erased do
        throwError "aesop: {decl} is not registered as an Aesop rule."
      setEnv $ ← ext.setState (← getEnv) rss
  }
  -- Despite the name, this also works for non-builtin attributes.
  registerBuiltinAttribute impl
  return ext

def getAttributeRuleSets [MonadEnv m] : m RuleSets := do
  extension.getState (← getEnv)

def modifyAttributeRuleSets [MonadEnv m] (f : RuleSets → m RuleSets) : m Unit := do
  let env ← getEnv
  let rss ← extension.getState env
  let rss ← f rss
  let env ← extension.setState env rss
  setEnv env

def getAttributeRuleSet (includeDefaultSimpLemmas : Bool)
    (rsNames : Array RuleSetName) : CoreM RuleSet := do
  let rss ← getAttributeRuleSets
  let mut result := rss.makeMergedRuleSet rsNames
  if includeDefaultSimpLemmas then
    let defaultSimpLemmas ← getSimpLemmas
    result :=
      { result with
        normSimpLemmas := defaultSimpLemmas.merge result.normSimpLemmas }
  return result

def isRuleSetDeclared [MonadEnv m] (rsName : RuleSetName) : m Bool := do
  let rss ← getAttributeRuleSets
  return rss.containsRuleSet rsName

def declareRuleSet [MonadEnv m] (rsName : RuleSetName) : m Unit := do
  if rsName == defaultRuleSetName then
    throwError "aesop: rule set name '{rsName}' is reserved for the default rule set"
  let rss ← getAttributeRuleSets
  if rss.containsRuleSet rsName then
    throwError "aesop: rule set '{rsName}' already declared"
  let env ← extension.setState (← getEnv) $ rss.addEmptyRuleSet rsName
  setEnv env

open Lean.Elab.Command in
@[commandElab Parser.Command.declareAesopRuleSets]
def elabDeclareAesopRuleSets : CommandElab
  | `(declare_aesop_rule_sets [ $rsNames:ident,* ]) =>
    (rsNames : Array Syntax).forM λ rsName => declareRuleSet rsName.getId
  | _ => unreachable!

end Config


namespace Parser.Tactic

declare_syntax_cat aesop_rule

syntax ident (aesop_prio)? (aesop_clause)* : aesop_rule

declare_syntax_cat aesop_tactic_clause

syntax ruleList := "[" aesop_rule,+,? "]"

declare_syntax_cat aesop_rule_set_spec

syntax "-" ident : aesop_rule_set_spec
syntax ident : aesop_rule_set_spec

syntax "(" &"unsafe" ruleList ")" : aesop_tactic_clause
syntax "(" &"safe"   ruleList ")" : aesop_tactic_clause
syntax "(" &"norm"   ruleList ")" : aesop_tactic_clause
syntax "(" &"options" term ")" : aesop_tactic_clause
syntax "(" &"rulesets" "[" aesop_rule_set_spec,+,? "]" ")" : aesop_tactic_clause

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
    let clauses ← clauses.mapM (Clause.parse (isLocalRule := true))
    let config ← RuleConfig.ofKindAndClauses (ruleKind prio) clauses
    return { ruleIdent := (← RuleIdent.ofName i.getId), config := config }
  | _ => unreachable!

protected def build (goal : MVarId) (r : AdditionalRule) :
    MetaM (MVarId × RuleSetMember) :=
  r.config.buildLocalRule goal r.ruleIdent

end AdditionalRule

inductive RuleSetSpec
  | enable (name : RuleSetName)
  | disable (name : RuleSetName)
  deriving Inhabited

namespace RuleSetSpec

def parse : Syntax → RuleSetSpec
  | `(aesop_rule_set_spec| - $r:ident) => disable r.getId
  | `(aesop_rule_set_spec|   $r:ident) => enable r.getId
  | _ => unreachable!

def name : RuleSetSpec → RuleSetName
  | disable n => n
  | enable  n => n

end RuleSetSpec

inductive TacticClause
  | additionalRules (rs : Array AdditionalRule)
  | options (opts : Aesop.Options)
  | ruleSets (rsSpecs : Array RuleSetSpec)

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
  | `(aesop_tactic_clause|(rulesets [$rsspecs:aesop_rule_set_spec,*])) => do
    let rss ← getAttributeRuleSets
    ruleSets <$> (rsspecs : Array Syntax).mapM λ stx => do
      let spec := RuleSetSpec.parse stx
      if ! (← isRuleSetDeclared spec.name) then
        throwError "aesop: no such rule set: {spec.name}"
      return spec
  | _ => unreachable!

end TacticClause


structure TacticConfig where
  additionalRules : Array AdditionalRule := #[]
  options : Aesop.Options := {}
  enabledRuleSets : Array RuleSetName := defaultEnabledRuleSets
  deriving Inhabited

namespace TacticConfig

def addTacticClause (conf : TacticConfig) : TacticClause → TacticConfig
  | TacticClause.additionalRules rs =>
    { conf with additionalRules := conf.additionalRules ++ rs }
  | TacticClause.options opts =>
    { conf with options := opts }
  | TacticClause.ruleSets rsSpecs =>
    let rss :=
      rsSpecs.foldl (init := conf.enabledRuleSets) λ rss spec =>
        match spec with
        | RuleSetSpec.enable rsName =>
          if rss.contains rsName then rss else rss.push rsName
        | RuleSetSpec.disable rsName =>
          rss.filter (· != rsName)
    { conf with enabledRuleSets := rss }

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
  let mut rules := Array.mkEmpty c.additionalRules.size
  for r in c.additionalRules do
    let (goal', rule) ← r.build goal
    goal := goal'
    rules := rules.push rule
  return (goal, rules)

end TacticConfig

end Aesop.Config
