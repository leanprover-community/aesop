/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.ElabM
import Aesop.Percent
import Aesop.Rule.Name
import Aesop.Builder.Cases
import Aesop.Builder.Default
import Aesop.Builder.Forward
import Aesop.Builder.Unfold
import Aesop.RuleSet.Filter

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term


variable [Monad m] [MonadError m]


namespace Aesop.Frontend

namespace Parser

declare_syntax_cat Aesop.priority

syntax num "%" : Aesop.priority
syntax "-"? num : Aesop.priority

end Parser

inductive Priority
  | int (i : Int)
  | percent (p : Percent)
  deriving Inhabited

namespace Priority

def «elab» (stx : Syntax) : ElabM Priority :=
  withRef stx do
    unless ← shouldParsePriorities do throwError
      "unexpected priority."
    match stx with
    | `(priority| $p:num %) =>
      let p := p.raw.toNat
      match Percent.ofNat p with
      | some p => return percent p
      | none => throwError "percentage '{p}%' is not between 0 and 100."
    | `(priority| - $i:num) =>
      return int $ - i.raw.toNat
    | `(priority| $i:num) =>
      return int i.raw.toNat
    | _ => throwUnsupportedSyntax

instance : ToString Priority where
  toString
    | int i => toString i
    | percent p => p.toHumanString

def toInt? : Priority → Option Int
  | int i => some i
  | _ => none

def toPercent? : Priority → Option Percent
  | percent p => some p
  | _ => none

end Priority



namespace Parser

declare_syntax_cat Aesop.phase (behavior := symbol)

syntax "safe" : Aesop.phase
syntax "norm" : Aesop.phase
syntax "unsafe" : Aesop.phase

end Parser

def PhaseName.«elab» (stx : Syntax) : ElabM PhaseName :=
  withRef stx do
    match stx with
    | `(phase| safe) => return .safe
    | `(phase| norm) => return .norm
    | `(phase| unsafe) => return .«unsafe»
    | _ => throwUnsupportedSyntax


namespace Parser

declare_syntax_cat Aesop.builder_name (behavior := symbol)

syntax "apply" : Aesop.builder_name
syntax "simp" : Aesop.builder_name
syntax "unfold" : Aesop.builder_name
syntax "tactic" : Aesop.builder_name
syntax "constructors" : Aesop.builder_name
syntax "forward" : Aesop.builder_name
syntax "destruct" : Aesop.builder_name
syntax "cases" : Aesop.builder_name
syntax "default" : Aesop.builder_name

end Parser

inductive DBuilderName
  | regular (b : BuilderName)
  | «default»
  deriving Inhabited

namespace DBuilderName

def «elab» (stx : Syntax) : ElabM DBuilderName :=
  withRef stx do
    match stx with
    | `(builder_name| apply) => return regular .apply
    | `(builder_name| simp) => return regular .simp
    | `(builder_name| unfold) => return regular .unfold
    | `(builder_name| tactic) => return regular .tactic
    | `(builder_name| constructors) => return regular .constructors
    | `(builder_name| forward) => return regular .forward
    | `(builder_name| destruct) => return regular .destruct
    | `(builder_name| cases) => return regular .cases
    | `(builder_name| default) => return «default»
    | _ => throwUnsupportedSyntax

instance : ToString DBuilderName where
  toString
    | regular b => toString b
    | default => "default"

def toBuilderName? : DBuilderName → Option BuilderName
  | regular b => some b
  | _ => none

def toRuleBuilder : DBuilderName → RuleBuilder
  | .regular .apply => RuleBuilder.apply
  | .regular .cases => RuleBuilder.cases
  | .regular .constructors => RuleBuilder.constructors
  | .regular .destruct => RuleBuilder.forward (isDestruct := true)
  | .regular .forward => RuleBuilder.forward (isDestruct := false)
  | .regular .simp => RuleBuilder.simp
  | .regular .tactic => RuleBuilder.tactic
  | .regular .unfold => RuleBuilder.unfold
  | .default => RuleBuilder.default

end DBuilderName


namespace Parser

declare_syntax_cat Aesop.indexing_mode (behavior := symbol)

syntax "target " term : Aesop.indexing_mode
syntax "hyp " term : Aesop.indexing_mode
syntax "unindexed " : Aesop.indexing_mode

end Parser

def elabSingleIndexingMode (stx : Syntax) : ElabM IndexingMode :=
  withRef stx do
    match stx with
    | `(indexing_mode| target $t:term) => .target <$> elabKeys t
    | `(indexing_mode| hyp $t:term) => .hyps <$> elabKeys t
    | `(indexing_mode| unindexed) => return .unindexed
    | _ => throwUnsupportedSyntax
  where
    elabKeys (stx : Syntax) : ElabM (Array DiscrTree.Key) :=
      show TermElabM _ from withoutModifyingState do
        let e ← elabPattern stx
        DiscrTree.mkPath (← instantiateMVars e) discrTreeConfig

def IndexingMode.elab (stxs : Array Syntax) : ElabM IndexingMode :=
  .or <$> stxs.mapM elabSingleIndexingMode

def CasesPattern.elab (stx : Syntax) : TermElabM CasesPattern := do
  abstractMVars (← elabPattern stx)


namespace Parser

syntax transparency := &"default" <|> &"reducible" <|> &"instances" <|> &"all"

end Parser

open Parser in
def elabTransparency : TSyntax ``transparency → TermElabM TransparencyMode
  | `(transparency| default) => return .default
  | `(transparency| reducible) => return .reducible
  | `(transparency| instances) => return .instances
  | `(transparency| all) => return .all
  | _ => throwUnsupportedSyntax

namespace Parser

declare_syntax_cat Aesop.builder_option

syntax " (" &"immediate" " := " "[" ident,+,? "]" ")" : Aesop.builder_option
syntax " (" &"index" " := " "[" Aesop.indexing_mode,+,? "]" ")" : Aesop.builder_option
syntax " (" &"pattern" " := " term ")" : Aesop.builder_option
syntax " (" &"cases_patterns" " := " "[" term,+,? "]" ")" : Aesop.builder_option
syntax " (" &"transparency" " := " transparency ")" : Aesop.builder_option
syntax " (" &"transparency!" " := " transparency ")" : Aesop.builder_option

end Parser

inductive BuilderOption
  | immediate (names : Array Name)
  | index (imode : IndexingMode)
  | pattern (stx : Term)
  | casesPatterns (pats : Array CasesPattern)
  | transparency (md : TransparencyMode) (alsoForIndex : Bool)

namespace BuilderOption

def «elab» (stx : TSyntax `Aesop.builder_option) : ElabM BuilderOption :=
  withRef stx do
    match stx with
    | `(builder_option| (immediate := [$ns:ident,*])) =>
      return immediate $ (ns : Array Syntax).map (·.getId)
    | `(builder_option| (index := [$imodes:Aesop.indexing_mode,*])) =>
      index <$> IndexingMode.elab imodes
    | `(builder_option| (pattern := $pat:term)) =>
      return pattern pat
    | `(builder_option| (cases_patterns := [$pats:term,*])) =>
      casesPatterns <$> (pats : Array Syntax).mapM (CasesPattern.elab ·)
    | `(builder_option| (transparency := $md)) =>
      let md ← elabTransparency md
      return transparency md (alsoForIndex := false)
    | `(builder_option| (transparency! := $md)) =>
      let md ← elabTransparency md
      return transparency md (alsoForIndex := true)
    | _ => throwUnsupportedSyntax

end BuilderOption



def addBuilderOption (bos : RuleBuilderOptions) :
    BuilderOption → RuleBuilderOptions
  | .immediate ns => { bos with immediatePremises? := ns }
  | .index imode => { bos with indexingMode? := imode }
  | .pattern pat => { bos with pattern? := pat }
  | .casesPatterns ps => { bos with casesPatterns? := ps }
  | .transparency md alsoForIndex =>
    let bos := { bos with transparency? := md }
    if alsoForIndex then
      { bos with indexTransparency? := md }
    else
      bos


namespace Parser

syntax ruleSetsFeature := "(" &"rule_sets" " := " "[" ident,+,? "]" ")"

end Parser

def RuleSetName.elab (stx : Syntax) : RuleSetName :=
  stx.getId.eraseMacroScopes
  -- We erase macro scopes to support macros such as
  --   macro &"aesop_test" : tactic => `(tactic| aesop (rule_sets [test]))
  -- Here the macro hygienifies `test` by appending macro scopes, but we want
  -- to interpret `test` as a global name.

structure RuleSets where
  ruleSets : Array RuleSetName
  deriving Inhabited

namespace RuleSets

def «elab» (stx : Syntax) : ElabM RuleSets :=
  withRef stx do
    match stx with
    | `(Parser.ruleSetsFeature| (rule_sets := [$ns:ident,*])) =>
      return ⟨(ns : Array Syntax).map RuleSetName.elab⟩
    | _ => throwUnsupportedSyntax

end RuleSets


namespace Parser

declare_syntax_cat Aesop.feature (behavior := symbol)

-- NOTE: This grammar has overlapping rules `ident`, `Aesop.phase` and
-- `Aesop.builder_name`, which can all consist of a single ident. For ambiguous
-- parses, a `choice` node with two children is created; one being an
-- `Aesop.phase` or `Aesop.builder_name` node and the other being a `featIdent`
-- node. When we process these `choice` nodes, we select the non-`ident` one.

syntax Aesop.phase : Aesop.feature
syntax Aesop.priority : Aesop.feature
syntax Aesop.builder_name : Aesop.feature
syntax Aesop.builder_option : Aesop.feature
syntax ruleSetsFeature : Aesop.feature
syntax (name := featIdent) ident : Aesop.feature
syntax "(" term ")" : Aesop.feature

end Parser

inductive Feature
  | phase (p : PhaseName)
  | priority (p : Priority)
  | builder (b : DBuilderName)
  | builderOption (o : BuilderOption)
  | term (i : Term)
  | ruleSets (rs : RuleSets)
  deriving Inhabited

namespace Feature

partial def «elab» (stx : Syntax) : ElabM Feature :=
  withRef stx do
    match stx with
    | `(feature| $p:Aesop.priority) => priority <$> Priority.elab p
    | `(feature| $p:Aesop.phase) => phase <$> PhaseName.elab p
    | `(feature| $b:Aesop.builder_name) => builder <$> DBuilderName.elab b
    | `(feature| $o:Aesop.builder_option) => builderOption <$> BuilderOption.elab o
    | `(feature| $rs:ruleSetsFeature) => ruleSets <$> RuleSets.elab rs
    | `(feature| $i:ident) => return term i
    | `(feature| ($t:term)) => return term t
    | stx => do
      if stx.isOfKind choiceKind then
        let nonIdentAlts :=
          stx.getArgs.filter λ stx => ! stx.isOfKind ``Parser.featIdent
        if h : nonIdentAlts.size = 1 then
          return ← «elab» $ nonIdentAlts[0]'(by simp [h])
      throwUnsupportedSyntax

end Feature


namespace Parser

declare_syntax_cat Aesop.rule_expr (behavior := symbol)

syntax Aesop.feature : Aesop.rule_expr
syntax Aesop.feature ppSpace Aesop.rule_expr : Aesop.rule_expr
syntax Aesop.feature " [" Aesop.rule_expr,+,? "]" : Aesop.rule_expr

end Parser


inductive RuleExpr
  | node (f : Feature) (children : Array RuleExpr)
  deriving Inhabited

namespace RuleExpr

partial def «elab» (stx : Syntax) : ElabM RuleExpr :=
  withRef stx do
    match stx with
    | `(rule_expr| $f:Aesop.feature $e:Aesop.rule_expr) => do
      return node (← Feature.elab f) #[← «elab» e]
    | `(rule_expr| $f:Aesop.feature [ $es:Aesop.rule_expr,* ]) => do
      return node (← Feature.elab f) (← (es : Array Syntax).mapM «elab»)
    | `(rule_expr| $f:Aesop.feature) => do
      return node (← Feature.elab f) #[]
    | _ => throwUnsupportedSyntax

-- Fold the branches of a `RuleExpr`. We treat each branch as a list of features
-- which we fold over. The result is an array containing one result per branch.
partial def foldBranchesM {m} [Monad m] (f : σ → Feature → m σ) (init : σ)
    (e : RuleExpr) : m (Array σ) :=
  go init #[] e
  where
    go (c : σ) (acc : Array σ) : RuleExpr → m (Array σ)
      | RuleExpr.node feat cs => do
        let c ← f c feat
        if cs.isEmpty then
          return acc.push c
        else
          cs.foldlM (init := acc) (go c)

end RuleExpr

structure RuleConfig where
  term? : Option Term
  phase? : Option PhaseName
  priority? : Option Priority
  builder? : Option DBuilderName
  builderOptions : RuleBuilderOptions
  ruleSets : RuleSets

namespace RuleConfig

def addFeature (c : RuleConfig) : Feature → m RuleConfig
  | .phase phase => return { c with phase? := phase }
  | .priority priority => return { c with priority? := priority }
  | .term term => do
    if let some oldTerm := c.term? then
      throwError "duplicate rule '{term}'; rule '{oldTerm}' was already given.\nUse [<term>,...] to give multiple rules."
    return { c with term? := term }
  | .builder builder => return { c with builder? := builder }
  | .builderOption opt =>
    return { c with builderOptions := addBuilderOption c.builderOptions opt }
  | .ruleSets newRuleSets =>
    have _ : Ord RuleSetName := ⟨Name.quickCmp⟩
    let ruleSets := ⟨Array.mergeDedup c.ruleSets.ruleSets newRuleSets.ruleSets.qsortOrd⟩
    return { c with ruleSets := ruleSets }

def getPenalty (phase : PhaseName) (c : RuleConfig) : m Int := do
  let (some priority) := c.priority? | throwError
    "{phase} rules must specify an integer penalty"
  let (some penalty) := priority.toInt? | throwError
    "{phase} rules must specify an integer penalty (not a success probability)"
  return penalty

def getSuccessProbability (c : RuleConfig) : m Percent := do
  let (some priority) := c.priority? | throwError
    "unsafe rules must specify a success probability"
  let (some prob) := priority.toPercent? | throwError
    "unsafe rules must specify a success probability (not an integer penalty)"
  return prob

def getSimpPriority (c : RuleConfig) : m Nat := do
  let prio? := do
    let priority ← (← c.priority?).toInt?
    guard $ priority ≥ 0
    return priority.toNat
  let (some prio) := prio? | throwError
    "simp rules must specify a non-negative integer priority"
  return prio

def getTerm (c : RuleConfig) : m Term := do
  let some term := c.term? | throwError
    "missing rule"
  return term

def getPhase (c : RuleConfig) : m PhaseName := do
  let some phase := c.phase? | throwError
    "missing phase (norm/safe/unsafe)"
  return phase

def getBuilder (c : RuleConfig) : m DBuilderName := do
  let some builder := c.builder? | throwError
    "missing rule builder (apply, forward, simp, ...)"
  return builder

def getPhaseSpec (c : RuleConfig) : m PhaseSpec := do
  match ← c.getPhase with
  | .safe =>
    return .safe { penalty := ← c.getPenalty .safe, safety := .safe }
  | .unsafe =>
    return .unsafe { successProbability := ← c.getSuccessProbability }
  | .norm =>
    return .norm { penalty := ← c.getPenalty .norm }

def getRuleBuilderInput (c : RuleConfig) : TermElabM RuleBuilderInput := do
  let term ← c.getTerm
  let phase ← c.getPhaseSpec
  let options := c.builderOptions
  return { term, options, phase }

def buildRule (c : RuleConfig) :
    ElabM (LocalRuleSetMember × Array RuleSetName) := do
  let builder ← c.getBuilder
  let builderInput ← c.getRuleBuilderInput
  let ruleSetMember ← builder.toRuleBuilder builderInput
  return (ruleSetMember, c.ruleSets.ruleSets)

def buildGlobalRule (c : RuleConfig) :
    ElabM (GlobalRuleSetMember × Array RuleSetName) := do
  let (m, rsNames) ← buildRule c
  if let some m := m.toGlobalRuleSetMember? then
    return (m, rsNames)
  else
    throwError "internal error: buildGlobalRule: unexpected local rule"

def buildLocalRule (c : RuleConfig) : ElabM LocalRuleSetMember :=
  (·.fst) <$> c.buildRule

def toRuleFilter (c : RuleConfig) : ElabM (RuleSetNameFilter × RuleFilter) := do
  let term ← c.getTerm
  if ! term.raw.isIdent then
    throwError "erase rule must be a name, not a composite term"
  let some e ← resolveId? term
    | throwError "unknown identifier: {term}"
  let (name, scope) ←
    match e with
    | .const decl _ => pure (decl, .global)
    | .fvar fvarId => pure ((← fvarId.getDecl).userName, .local)
    | _ => throwError "internal error: expected const or fvar, but got '{e}'"
  let builders ←
    match c.builder? with
    | none => pure #[]
    | some b => do
      let (some builder) := b.toBuilderName? | throwError
        "{b} cannot be used when erasing rules.\nUse the corresponding non-default builder (e.g. 'apply' or 'constructors') instead."
        -- We could instead look for the correct non-default builder ourselves
        -- by re-running the logic that determines which builder to use.
      pure #[builder]
  let phases :=
    match c.phase? with
    | none => #[]
    | some p => #[p]
  let ruleSetNames := c.ruleSets.ruleSets
  return ({ ns := ruleSetNames }, { name, scope, builders, phases })

def validateForAdditionalRules (c : RuleConfig) (defaultRuleSet : RuleSetName) :
    m RuleConfig := do
  let term ← c.getTerm
  let (phase, priority) ← getPhaseAndPriority c
  let builder := c.builder?.getD .default
  let builderOptions := c.builderOptions
  let ruleSets :=
    if c.ruleSets.ruleSets.isEmpty then
      ⟨#[defaultRuleSet]⟩
    else
      c.ruleSets
  return {
    term? := term
    phase? := phase
    priority? := priority
    builder? := builder
    builderOptions, ruleSets
  }
where
  getPhaseAndPriority (c : RuleConfig) : m (PhaseName × Priority) :=
    match c.builder?, c.phase?, c.priority? with
    | _, some phase, some prio =>
      return (phase, prio)
    | some (.regular .simp), none, none =>
      return (.norm, .int defaultSimpRulePriority)
    | some (.regular .simp), none, some prio =>
      return (.norm, prio)
    | some (.regular .simp), some phase, none =>
      return (phase, .int defaultSimpRulePriority)
    | _, some .unsafe, none =>
      return (.unsafe, .percent defaultSuccessProbability)
    | _, some .safe, none =>
      return (.safe, .int defaultSafePenalty)
    | _, some .norm, none =>
      return (.norm, .int defaultNormPenalty)
    | _, none, some prio@(.percent _) =>
      return (.unsafe, prio)
    | _, none, _ =>
      throwError "phase (safe/unsafe/norm) not specified."

end RuleConfig


namespace RuleExpr

def toRuleConfigs (e : RuleExpr) (init : RuleConfig) :
    m (Array RuleConfig) :=
  e.foldBranchesM (init := init) λ c feature => c.addFeature feature

def toAdditionalRules (e : RuleExpr) (init : RuleConfig)
    (defaultRuleSet : RuleSetName) : m (Array RuleConfig) := do
  let cs ← e.toRuleConfigs init
  cs.mapM (·.validateForAdditionalRules defaultRuleSet)

def toAdditionalGlobalRules (decl? : Option Name) (e : RuleExpr) :
    m (Array RuleConfig) :=
  let init := {
    term? := decl?.map (mkIdent ·)
    phase? := none
    priority? := none
    builder? := none
    builderOptions := ∅
    ruleSets := ⟨#[]⟩
  }
  toAdditionalRules e init defaultRuleSetName

def buildAdditionalGlobalRules (decl? : Option Name) (e : RuleExpr) :
    TermElabM (Array (GlobalRuleSetMember × Array RuleSetName)) := do
  let go : ElabM _ := do
    (← e.toAdditionalGlobalRules decl?).mapM (·.buildGlobalRule)
  go.run $ ← ElabM.Context.forAdditionalGlobalRules

def toAdditionalLocalRules (e : RuleExpr) : MetaM (Array RuleConfig) :=
  let init := {
    term? := none
    phase? := none
    priority? := none
    builder? := none
    builderOptions := ∅
    ruleSets := ⟨#[]⟩
  }
  toAdditionalRules e init localRuleSetName

def buildAdditionalLocalRules (goal : MVarId) (e : RuleExpr) :
    TermElabM (Array LocalRuleSetMember) :=
  let go : ElabM _ := do (← e.toAdditionalLocalRules).mapM (·.buildLocalRule)
  go.run $ .forAdditionalRules goal

def toRuleFilters (e : RuleExpr) :
    ElabM (Array (RuleSetNameFilter × RuleFilter)) := do
  let initialConfig := {
      term? := none
      phase? := none
      priority? := none
      builder? := none
      builderOptions := ∅
      ruleSets := ⟨#[]⟩
  }
  let configs ← e.toRuleConfigs initialConfig
  configs.mapM (·.toRuleFilter)

def toGlobalRuleFilters (e : RuleExpr) :
    TermElabM (Array (RuleSetNameFilter × RuleFilter)) := do
  e.toRuleFilters |>.run $ ← ElabM.Context.forGlobalErasing

def toLocalRuleFilters (e : RuleExpr) : ElabM (Array RuleFilter) :=
  return (← e.toRuleFilters).map (·.snd)

end Aesop.Frontend.RuleExpr
