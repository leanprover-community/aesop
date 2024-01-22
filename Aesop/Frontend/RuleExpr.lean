/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Basic
import Aesop.Frontend.ElabM
import Aesop.Percent
import Aesop.Rule.Name
import Aesop.Builder
import Aesop.RuleSet

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
    unless (← read).parsePriorities do throwError
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
  | .regular .destruct => RuleBuilder.destruct
  | .regular .forward => RuleBuilder.forward
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

def elabPattern (stx : Syntax) : TermElabM Expr :=
  withRef stx $ withReader adjustCtx $ withSynthesize do
    instantiateMVars (← elabTerm stx none)
  where
    adjustCtx (old : Term.Context) : Term.Context := {
      old with
      mayPostpone := false
      errToSorry := false
      autoBoundImplicit := false
      sectionVars := {}
      sectionFVars := {}
      inPattern := true
    }

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
        DiscrTree.mkPath e discrTreeConfig

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
syntax " (" &"cases_patterns" " := " "[" term,+,? "]" ")" : Aesop.builder_option
syntax " (" &"transparency" " := " transparency ")" : Aesop.builder_option
syntax " (" &"transparency!" " := " transparency ")" : Aesop.builder_option

end Parser

inductive BuilderOption
  | immediate (names : Array Name)
  | index (imode : IndexingMode)
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
  | .casesPatterns ps => { bos with casesPatterns? := ps }
  | .transparency md alsoForIndex =>
    let bos := { bos with transparency? := md }
    if alsoForIndex then
      { bos with indexTransparency? := md }
    else
      bos


namespace Parser

syntax ruleSetsFeature := "(" &"rule_sets " "[" ident,+,? "]" ")"

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
    | `(Parser.ruleSetsFeature| (rule_sets [$ns:ident,*])) =>
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

end Parser

inductive Feature
  | phase (p : PhaseName)
  | priority (p : Priority)
  | builder (b : DBuilderName)
  | builderOption (o : BuilderOption)
  | ident (i : RuleIdent)
  | ruleSets (rs : RuleSets)
  deriving Inhabited

namespace Feature

private def elabRuleIdent (stx : Syntax) : ElabM RuleIdent :=
  resolveLocal <|> resolveGlobal <|> throwError
    "unknown rule name: {stx.getId}"
  where
    resolveLocal : ElabM RuleIdent := do
      let n := stx.getId.eraseMacroScopes
      match (← getLCtx).findFromUserName? n with
      | some ldecl =>
        if ldecl.isImplementationDetail then
          throwError ""
        else
          return .fvar n
      | none => throwError ""

    resolveGlobal : ElabM RuleIdent := do
      .const <$> resolveGlobalConstNoOverload stx

partial def «elab» (stx : Syntax) : ElabM Feature :=
  withRef stx do
    match stx with
    | `(feature| $p:Aesop.priority) => priority <$> Priority.elab p
    | `(feature| $p:Aesop.phase) => phase <$> PhaseName.elab p
    | `(feature| $b:Aesop.builder_name) => builder <$> DBuilderName.elab b
    | `(feature| $o:Aesop.builder_option) => builderOption <$> BuilderOption.elab o
    | `(feature| $rs:ruleSetsFeature) => ruleSets <$> RuleSets.elab rs
    | `(feature| $i:ident) => ident <$> elabRuleIdent i
    | stx =>
      if stx.isOfKind choiceKind then
        let nonIdentAlts :=
          stx.getArgs.filter λ stx => ! stx.isOfKind ``Parser.featIdent
        if nonIdentAlts.size != 1 then
          panic! "expected choice node with exactly one non-ident child"
        else
          «elab» nonIdentAlts[0]!
      else
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


structure RuleConfig (f : Type → Type) where
  ident : f RuleIdent
  phase : f PhaseName
  priority : f Priority
  builder : f DBuilderName
  builderOptions : RuleBuilderOptions
  ruleSets : RuleSets

namespace RuleConfig

def addFeature (c : RuleConfig Option) : Feature → RuleConfig Option
  | .phase phase => { c with phase }
  | .priority priority => { c with priority }
  | .ident ident => { c with ident }
  | .builder builder => { c with builder }
  | .builderOption opt =>
    { c with builderOptions := addBuilderOption c.builderOptions opt }
  | .ruleSets newRuleSets =>
    have _ : Ord RuleSetName := ⟨Name.quickCmp⟩
    let ruleSets :=
      ⟨Array.mergeSortedDeduplicating c.ruleSets.ruleSets
        newRuleSets.ruleSets.qsortOrd⟩
    { c with ruleSets }

def getPenalty (phase : PhaseName) (c : RuleConfig Id) : m Int := do
  let (some penalty) := c.priority.toInt? | throwError
    "{phase} rules must specify an integer penalty (not a success probability)"
  return penalty

def getSuccessProbability (c : RuleConfig Id) : m Percent := do
  let (some prob) := c.priority.toPercent? | throwError
    "unsafe rules must specify a success probability (not an integer penalty)"
  return prob

def getSimpPriority (c : RuleConfig Id) : m Nat := do
  let prio? := c.priority.toInt?.bind λ prio =>
    if prio < 0 then none else some prio.toNat
  let (some prio) := prio? | throwError
    "simp rules must specify a non-negative integer priority"
  return prio

def buildLocalRule (c : RuleConfig Id) (goal : MVarId) :
    MetaM (MVarId × RuleSetMember × Array RuleSetName) := do
  match c.phase with
  | phase@PhaseName.safe =>
    let penalty ← c.getPenalty phase
    let (goal, res) ← runRegularBuilder goal phase c.builder
    let rule := RuleSetMember.safeRule {
      name := c.ident.toRuleName phase res.builder
      tac := res.tac
      indexingMode := res.indexingMode
      extra := { penalty, safety := Safety.safe }
      pattern? := none -- TODO
    }
    return (goal, rule, c.ruleSets.ruleSets)
  | phase@PhaseName.«unsafe» =>
    let successProbability ← c.getSuccessProbability
    let (goal, res) ← runRegularBuilder goal phase c.builder
    let rule := RuleSetMember.unsafeRule {
      name := c.ident.toRuleName phase res.builder
      tac := res.tac
      indexingMode := res.indexingMode
      extra := { successProbability }
      pattern? := none -- TODO
    }
    return (goal, rule, c.ruleSets.ruleSets)
  | phase@PhaseName.norm =>
    let (goal, res) ← runBuilder goal phase c.builder
    let rule ←
      match res with
      | .regular res => do
        let penalty ← c.getPenalty phase
        pure $ .normRule {
          res with
          name := c.ident.toRuleName phase res.builder
          extra := { penalty }
          pattern? := none -- TODO
        }
      | .globalSimp entries => do
        let prio ← c.getSimpPriority
        let entries := entries.map (updateSimpEntryPriority prio)
        pure $ .normSimpRule {
          entries
          name := c.ident.toRuleName phase .simp
        }
      | .localSimp fvarUserName => pure $ .localNormSimpRule { fvarUserName }
      | .unfold r => pure $ .unfoldRule r
    return (goal, rule, c.ruleSets.ruleSets)
  where
    runBuilder (goal : MVarId) (phase : PhaseName) (b : DBuilderName) :
        MetaM (MVarId × RuleBuilderResult) := do
      let builderInput : RuleBuilderInput :=
        match c.ident with
        | RuleIdent.const decl => {
            phase := phase
            kind := RuleBuilderKind.global decl
            options := c.builderOptions
          }
        | RuleIdent.fvar fvarUserName => {
            phase := phase
            kind := RuleBuilderKind.local fvarUserName goal
            options := c.builderOptions
          }
      match ← b.toRuleBuilder builderInput with
      | .global r => return (goal, r)
      | .«local» goal r => return (goal, r)

    runRegularBuilder (goal : MVarId) (phase : PhaseName) (b : DBuilderName) :
        MetaM (MVarId × RegularRuleBuilderResult) := do
      let (goal, RuleBuilderResult.regular r) ← runBuilder goal phase b
        | throwError "builder {b} cannot be used for {phase} rules"
      return (goal, r)

-- Precondition: `c.ident = RuleIdent.const _`.
def buildGlobalRule (c : RuleConfig Id) :
    MetaM (RuleSetMember × Array RuleSetName) :=
  Prod.snd <$> buildLocalRule c ⟨`_dummy⟩
  -- NOTE: We assume here that global rule builders ignore the dummy
  -- metavariable.

def toRuleNameFilter (c : RuleConfig Option) :
    m (RuleSetNameFilter × RuleNameFilter) := do
  let (some ident) := c.ident | throwError
    "rule name not specified"
  let builders ←
    match c.builder with
    | none => pure #[]
    | some b => do
      let (some builder) := b.toBuilderName? | throwError
        "{b} cannot be used when erasing rules.\nUse the corresponding non-default builder (e.g. 'apply' or 'constructors') instead."
        -- We could instead look for the correct non-default builder ourselves
        -- by re-running the logic that determines which builder to use.
      pure #[builder]
  let phases :=
    match c.phase with
    | none => #[]
    | some p => #[p]
  let ruleSetNames := c.ruleSets.ruleSets
  return ({ ns := ruleSetNames }, { ident, builders, phases })

end RuleConfig


namespace RuleExpr

def toRuleConfigs (e : RuleExpr) (init : RuleConfig Option) :
    Array (RuleConfig Option) :=
  e.foldBranchesM (m := Id) (init := init) λ c feature => c.addFeature feature

def toAdditionalRules (e : RuleExpr) (init : RuleConfig Option)
    (defaultRuleSet : RuleSetName) : m (Array (RuleConfig Id)) := do
  let cs := e.toRuleConfigs init
  cs.mapM finish
  where
    getPhaseAndPriority (c : RuleConfig Option) :
        m (PhaseName × Priority) :=
      match c.builder, c.phase, c.priority with
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

    finish (c : RuleConfig Option) : m (RuleConfig Id) := do
      let (some ident) := c.ident | throwError
        "rule name not specified"
      let (phase, priority) ← getPhaseAndPriority c
      let builder := c.builder.getD .default
      let builderOptions := c.builderOptions
      let ruleSets :=
        if c.ruleSets.ruleSets.isEmpty then
          ⟨#[defaultRuleSet]⟩
        else
          c.ruleSets
      return { ident, phase, priority, builder, builderOptions, ruleSets }

def toAdditionalGlobalRules (decl : Name) (e : RuleExpr) :
    m (Array (RuleConfig Id)) :=
  let init := {
    ident := RuleIdent.const decl
    phase := none
    priority := none
    builder := none
    builderOptions := ∅
    ruleSets := ⟨#[]⟩
  }
  toAdditionalRules e init defaultRuleSetName

def buildAdditionalGlobalRules (decl : Name) (e : RuleExpr) :
    MetaM (Array (RuleSetMember × Array RuleSetName)) := do
  (← e.toAdditionalGlobalRules decl).mapM (·.buildGlobalRule)

def toAdditionalLocalRules (goal : MVarId) (e : RuleExpr) :
    MetaM (Array (RuleConfig Id)) :=
  goal.withContext do
    let init := {
      ident := none
      phase := none
      priority := none
      builder := none
      builderOptions := ∅
      ruleSets := ⟨#[]⟩
    }
    toAdditionalRules e init localRuleSetName

def buildAdditionalLocalRules (goal : MVarId) (e : RuleExpr) :
    MetaM (MVarId × Array (RuleSetMember × Array RuleSetName)) := do
  let configs ← e.toAdditionalLocalRules goal
  let mut goal := goal
  let mut rs := Array.mkEmpty configs.size
  for config in configs do
    let (goal', rule) ← config.buildLocalRule goal
    goal := goal'
    rs := rs.push rule
  return (goal, rs)

def toRuleNameFilters (e : RuleExpr) :
    m (Array (RuleSetNameFilter × RuleNameFilter)) := do
  let initialConfig := {
      ident := none
      phase := none
      priority := none
      builder := none
      builderOptions := ∅
      ruleSets := ⟨#[]⟩
  }
  let configs := e.toRuleConfigs initialConfig
  configs.mapM (·.toRuleNameFilter)

def toGlobalRuleNameFilters (e : RuleExpr) :
    m (Array (RuleSetNameFilter × RuleNameFilter)) :=
  e.toRuleNameFilters

def toLocalRuleNameFilters (goal : MVarId) (e : RuleExpr) :
    MetaM (Array (RuleSetNameFilter × RuleNameFilter)) :=
  goal.withContext $ e.toRuleNameFilters

end Aesop.Frontend.RuleExpr
