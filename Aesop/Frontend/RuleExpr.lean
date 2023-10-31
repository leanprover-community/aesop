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

syntax " (" &"uses_branch_state" " := " Aesop.bool_lit ")" : Aesop.builder_option
syntax " (" &"immediate" " := " "[" ident,+,? "]" ")" : Aesop.builder_option
syntax " (" &"index" " := " "[" Aesop.indexing_mode,+,? "]" ")" : Aesop.builder_option
syntax " (" &"patterns" " := " "[" term,+,? "]" ")" : Aesop.builder_option
syntax " (" &"transparency" " := " transparency ")" : Aesop.builder_option
syntax " (" &"transparency!" " := " transparency ")" : Aesop.builder_option

syntax builderOptions := Aesop.builder_option*

end Parser

inductive BuilderOption
  | immediate (names : Array Name)
  | index (imode : IndexingMode)
  | patterns (pats : Array CasesPattern)
  | transparency (md : TransparencyMode) (alsoForIndex : Bool)

namespace BuilderOption

def «elab» (stx : TSyntax `Aesop.builder_option) : ElabM BuilderOption :=
  withRef stx do
    match stx with
    | `(builder_option| (immediate := [$ns:ident,*])) =>
      return immediate $ (ns : Array Syntax).map (·.getId)
    | `(builder_option| (index := [$imodes:Aesop.indexing_mode,*])) =>
      index <$> IndexingMode.elab imodes
    | `(builder_option| (patterns := [$pats:term,*])) =>
      patterns <$> (pats : Array Syntax).mapM (CasesPattern.elab ·)
    | `(builder_option| (transparency := $md)) =>
      let md ← elabTransparency md
      return transparency md (alsoForIndex := false)
    | `(builder_option| (transparency! := $md)) =>
      let md ← elabTransparency md
      return transparency md (alsoForIndex := true)
    | _ => throwUnsupportedSyntax

protected def name : BuilderOption → String
  | immediate .. => "immediate"
  | index .. => "index"
  | patterns .. => "patterns"
  | transparency .. => "transparency"

protected def toCtorIdx : BuilderOption → Nat
  | immediate .. => 0
  | index .. => 1
  | patterns .. => 2
  | transparency .. => 3

end BuilderOption


structure BuilderOptions (σ : Type _) where
  builderName : DBuilderName
  init : σ
  add : σ → BuilderOption → Option σ

namespace BuilderOptions

def «elab» (bo : BuilderOptions α) (stx : Syntax) : ElabM α :=
  withRef stx do
    match stx with
    | `(Parser.builderOptions| $stxs:Aesop.builder_option*) => do
      let mut opts := bo.init
      let mut seen : HashSet Nat := {}
      for stx in stxs do
        let opt ← BuilderOption.elab stx
        let idx := opt.toCtorIdx
        if seen.contains idx then withRef stx $ throwError
          "duplicate builder option '{opt.name}'"
        seen := seen.insert idx
        match bo.add opts opt with
        | some opts' => opts := opts'
        | none => withRef stx $ throwError
          "builder '{bo.builderName}' does not accept option '{opt.name}'"
      return opts
    | _ => throwUnsupportedSyntax

protected def none (builderName : DBuilderName) : BuilderOptions Unit where
  builderName := builderName
  init := ()
  add _ _ := none

def regular (builderName : BuilderName) :
    BuilderOptions RegularBuilderOptions where
  builderName := .regular builderName
  init := default
  add
    | opts, .index imode => some { opts with indexingMode? := imode }
    | _, _ => none

@[inline, always_inline]
private def forwardCore (clear : Bool) :
    BuilderOptions ForwardBuilderOptions where
  builderName := .regular $ if clear then .destruct else .forward
  init := .default clear
  add
    | opts, .immediate ns => some { opts with immediateHyps := ns }
    | opts, .index imode => some { opts with indexingMode? := imode }
    | opts, .transparency transparency alsoForIndex =>
      let opts := { opts with transparency }
      if alsoForIndex then
        some { opts with indexTransparency := transparency }
      else
        some opts
    | _, _ => none

def forward : BuilderOptions ForwardBuilderOptions :=
  forwardCore (clear := false)

def destruct : BuilderOptions ForwardBuilderOptions :=
  forwardCore (clear := true)

def cases : BuilderOptions CasesBuilderOptions where
  builderName := .regular .cases
  init := default
  add
    | opts, .patterns patterns => some { opts with patterns }
    | opts, .index indexingMode? => some { opts with indexingMode? }
    | opts, .transparency transparency alsoForIndex =>
      let opts := { opts with transparency }
      if alsoForIndex then
        some { opts with indexTransparency := transparency }
      else
        some opts
    | _, _ => none

def apply : BuilderOptions ApplyBuilderOptions where
  builderName := .regular .cases
  init := default
  add
    | opts, .index indexingMode? => some { opts with indexingMode? }
    | opts, .transparency transparency alsoForIndex =>
      let opts := { opts with transparency }
      if alsoForIndex then
        some { opts with indexTransparency := transparency }
      else
        some opts
    | _, _ => none

def constructors : BuilderOptions ConstructorsBuilderOptions where
  builderName := .regular .cases
  init := default
  add
    | opts, .index indexingMode? => some { opts with indexingMode? }
    | opts, .transparency transparency alsoForIndex =>
      let opts := { opts with transparency }
      if alsoForIndex then
        some { opts with indexTransparency := transparency }
      else
        some opts
    | _, _ => none

end BuilderOptions


namespace Parser

declare_syntax_cat Aesop.builder (behavior := symbol)

syntax Aesop.builder_name : Aesop.builder
syntax "(" Aesop.builder_name builderOptions ")" : Aesop.builder

end Parser

inductive Builder
  | apply (opts : ApplyBuilderOptions)
  | simp
  | unfold
  | tactic (opts : RegularBuilderOptions)
  | constructors (opts : ConstructorsBuilderOptions)
  | forward (opts : ForwardBuilderOptions)
  | cases (opts : CasesBuilderOptions)
  | «default»
  deriving Inhabited

namespace Builder

def elabOptions (b : DBuilderName) (opts : Syntax) : ElabM Builder := do
  match b with
  | .regular .apply => apply <$> BuilderOptions.apply.elab opts
  | .regular .simp => checkNoOptions; return simp
  | .regular .unfold => checkNoOptions; return unfold
  | .regular .tactic => tactic <$> (BuilderOptions.regular .tactic |>.elab opts)
  | .regular .constructors => constructors <$> BuilderOptions.constructors.elab opts
  | .regular .forward => forward <$> BuilderOptions.forward.elab opts
  | .regular .destruct => forward <$> BuilderOptions.destruct.elab opts
  | .regular .cases => «cases» <$> BuilderOptions.cases.elab opts
  | .default => checkNoOptions; return default
  where
    checkNoOptions := BuilderOptions.none b |>.«elab» opts

def «elab» (stx : Syntax) : ElabM Builder :=
  withRef stx do
    match stx with
    | `(builder| $b:Aesop.builder_name) => do
      elabOptions (← DBuilderName.elab b) (mkNode ``Parser.builderOptions #[])
    | `(builder| ($b:Aesop.builder_name $opts:builderOptions)) => do
      elabOptions (← DBuilderName.elab b) opts
    | _ => throwUnsupportedSyntax

def toRuleBuilder : Builder → RuleBuilder
  | apply opts  => RuleBuilder.apply opts
  | simp => RuleBuilder.simp
  | unfold => RuleBuilder.unfold
  | tactic opts => RuleBuilder.tactic opts
  | constructors opts => RuleBuilder.constructors opts
  | forward opts => RuleBuilder.forward opts
  | cases opts => RuleBuilder.cases opts
  | «default» => RuleBuilder.default

open DBuilderName in
def toDBuilderName : Builder → DBuilderName
  | apply .. => regular .apply
  | simp => regular .simp
  | unfold => regular .unfold
  | tactic .. => regular .tactic
  | constructors .. => regular .constructors
  | forward .. => regular .forward
  | cases .. => regular .cases
  | .«default» => .default

end Builder

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

-- NOTE: This grammar has overlapping rules (`ident`, `Aesop.builder` and
-- `Aesop.phase` since they can all consist of a single ident). For ambiguous
-- parses, a `choice` node with two children is created; one being a
-- `featPhase` or `featBuilder` node and the second being a `featIdent` node.
-- When we process these `choice` nodes, we select the non-`ident` one.
syntax Aesop.phase : Aesop.feature
syntax Aesop.priority : Aesop.feature
syntax Aesop.builder : Aesop.feature
syntax ruleSetsFeature : Aesop.feature
syntax (name := featIdent) ident : Aesop.feature

end Parser

inductive Feature
  | phase (p : PhaseName)
  | priority (p : Priority)
  | builder (b : Builder)
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
    | `(feature| $b:Aesop.builder) => builder <$> Builder.elab b
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
  builder : f Builder
  ruleSets : RuleSets

namespace RuleConfig

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
      -- TODO support 'almost safe' rules
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
    runBuilder (goal : MVarId) (phase : PhaseName) (b : Builder) :
        MetaM (MVarId × RuleBuilderResult) := do
      let builderInput : RuleBuilderInput :=
        match c.ident with
        | RuleIdent.const decl => {
            phase := phase
            kind := RuleBuilderKind.global decl
          }
        | RuleIdent.fvar fvarUserName => {
            phase := phase
            kind := RuleBuilderKind.local fvarUserName goal
          }
      match ← b.toRuleBuilder builderInput with
      | .global r => return (goal, r)
      | .«local» goal r => return (goal, r)

    runRegularBuilder (goal : MVarId) (phase : PhaseName) (b : Builder) :
        MetaM (MVarId × RegularRuleBuilderResult) := do
      let (goal, RuleBuilderResult.regular r) ← runBuilder goal phase b
        | throwError "builder {b.toDBuilderName} cannot be used for {phase} rules"
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
      let (some builder) := b.toDBuilderName.toBuilderName? | throwError
        "{b.toDBuilderName} cannot be used when erasing rules.\nUse the corresponding non-default builder (e.g. 'apply' or 'constructors') instead."
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

def toAdditionalRules (e : RuleExpr) (init : RuleConfig Option)
    (defaultRuleSet : RuleSetName) : m (Array (RuleConfig Id)) := do
  let cs ← e.foldBranchesM (init := init) go
  cs.mapM finish
  where
    go (r : RuleConfig Option) : Feature → m (RuleConfig Option)
      | .phase p => do
        if let (some previous) := r.phase then throwError
          "duplicate phase declaration: '{p}'\n(previous declaration: '{previous}')"
        return { r with phase := some p }
      | .priority p => do
        if let (some previous) := r.priority then throwError
          "duplicate priority declaration: '{p}'\n(previous declaration: '{previous}')"
        return { r with priority := some p }
      | .builder b => do
        if let (some previous) := r.builder then throwError
          "duplicate builder declaration: '{b.toDBuilderName}'\n(previous declaration: '{previous.toDBuilderName}')"
        return { r with builder := some b }
      | .ident ident => do
        if let (some previous) := r.ident then throwError
          "duplicate rule name: '{ident}'\n(previous rule name: '{previous}')"
        return { r with ident }
      | .ruleSets newRuleSets =>
        have _ : Ord RuleSetName := ⟨Name.quickCmp⟩
        let ruleSets :=
          ⟨Array.mergeSortedDeduplicating r.ruleSets.ruleSets $
            newRuleSets.ruleSets.qsortOrd⟩
        return { r with ruleSets }

    getPhaseAndPriority (c : RuleConfig Option) :
        m (PhaseName × Priority) :=
      match c.builder, c.phase, c.priority with
      | _, some phase, some prio =>
        return (phase, prio)
      | some .simp, none, none =>
        return (.norm, .int defaultSimpRulePriority)
      | some .simp, none, some prio =>
        return (.norm, prio)
      | some .simp, some phase, none =>
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
      let ruleSets :=
        if c.ruleSets.ruleSets.isEmpty then
          ⟨#[defaultRuleSet]⟩
        else
          c.ruleSets
      return { ident, phase, priority, builder, ruleSets }

def toAdditionalGlobalRules (decl : Name) (e : RuleExpr) :
    m (Array (RuleConfig Id)) :=
  let init := {
    ident := RuleIdent.const decl
    phase := none
    priority := none
    builder := none
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
      ruleSets := ⟨#[]⟩
  }
  let configs ← e.foldBranchesM (init := initialConfig) go
  configs.mapM (·.toRuleNameFilter)
  where
    go (r : RuleConfig Option) : Feature → m (RuleConfig Option)
      | .phase p => do
        if let (some previous) := r.phase then throwError
          "duplicate phase declaration: '{p}'\n(previous declaration: '{previous}')"
        return { r with phase := some p }
      | .priority prio =>
        throwError "unexpected priority '{prio}'"
      | .ident ident => do
        if let (some previous) := r.ident then throwError
          "duplicate rule name: '{ident}'\n(previous rule name: '{previous}')"
        return { r with ident }
      | .builder b => do
        if let (some previous) := r.builder then throwError
          "duplicate builder declaration: '{b.toDBuilderName}'\n(previous declaration: '{previous.toDBuilderName}')"
        return { r with builder := some b }
      | .ruleSets newRuleSets =>
        have _ : Ord RuleSetName := ⟨Name.quickCmp⟩
        let ruleSets :=
          ⟨Array.mergeSortedDeduplicating r.ruleSets.ruleSets $
            newRuleSets.ruleSets.qsortOrd⟩
        return { r with ruleSets }

def toGlobalRuleNameFilters (e : RuleExpr) :
    m (Array (RuleSetNameFilter × RuleNameFilter)) :=
  e.toRuleNameFilters

def toLocalRuleNameFilters (goal : MVarId) (e : RuleExpr) :
    MetaM (Array (RuleSetNameFilter × RuleNameFilter)) :=
  goal.withContext $ e.toRuleNameFilters

end Aesop.Frontend.RuleExpr
