/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.RuleExpr
import Aesop.Options
import Batteries.Linter.UnreachableTactic
import Aesop.Frontend.Extension

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term

namespace Aesop.Frontend.Parser

declare_syntax_cat Aesop.tactic_clause

syntax ruleSetSpec := "-"? ident

syntax " (" &"add " Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax " (" &"erase " Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax " (" &"rule_sets" " := " "[" ruleSetSpec,+,? "]" ")" : Aesop.tactic_clause
syntax " (" &"config" " := " term ")" : Aesop.tactic_clause
syntax " (" &"simp_config" " := " term ")" : Aesop.tactic_clause

/--
`aesop <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[aesop]` attribute. See [its
README](https://github.com/JLimperg/aesop#readme) for a tutorial and a
reference.

The variant `aesop?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an Aesop call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an Aesop rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered Aesop rule. Example: `(erase
  Aesop.BuiltinRules.assumption)`.
- `(rule_sets := [<ruleset>,*])` enables or disables named sets of rules for
  this Aesop call. Example: `(rule_sets := [-builtin, MyRuleSet])`.
- `(config { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_config { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. The given options are directly passed to `simp`. For example,
  `(simp_config := { zeta := false })` makes Aesop use
  `simp (config := { zeta := false })`.
-/
syntax (name := aesopTactic)  "aesop"  Aesop.tactic_clause* : tactic

@[inherit_doc aesopTactic]
syntax (name := aesopTactic?) "aesop?" Aesop.tactic_clause* : tactic

initialize do
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``aesopTactic
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``aesopTactic?

end Parser

-- Inspired by declare_config_elab
unsafe def elabConfigUnsafe (type : Name) (stx : Syntax) : TermElabM α :=
  withRef stx do
    let e ← withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize <| withoutErrToSorry do
      let e ← Term.elabTermEnsuringType stx (Lean.mkConst type)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    evalExpr' α type e

def elabOptions : Syntax → TermElabM Aesop.Options :=
  unsafe elabConfigUnsafe ``Aesop.Options

def elabSimpConfig : Syntax → TermElabM Simp.Config :=
  unsafe elabConfigUnsafe ``Simp.Config

def elabSimpConfigCtx : Syntax → TermElabM Simp.ConfigCtx :=
  unsafe elabConfigUnsafe ``Simp.ConfigCtx

structure TacticConfig where
  additionalRules : Array RuleExpr
  erasedRules : Array RuleExpr
  enabledRuleSets : Std.HashSet RuleSetName
  options : Aesop.Options
  simpConfig : Simp.Config
  simpConfigSyntax? : Option Term

namespace TacticConfig

def parse (stx : Syntax) (goal : MVarId) : TermElabM TacticConfig :=
  withRef stx do
    match stx with
    | `(tactic| aesop $clauses:Aesop.tactic_clause*) =>
      go (traceScript := false) clauses
    | `(tactic| aesop? $clauses:Aesop.tactic_clause*) =>
      go (traceScript := true) clauses
    | _ => throwUnsupportedSyntax
  where
    go (traceScript : Bool) (clauses : Array (TSyntax `Aesop.tactic_clause)) :
        TermElabM TacticConfig := do
      let init : TacticConfig := {
        additionalRules := #[]
        erasedRules := #[]
        enabledRuleSets := ← getDefaultRuleSetNames
        options := { traceScript }
        simpConfig := {}
        simpConfigSyntax? := none
      }
      let (_, config) ← clauses.forM (addClause traceScript) |>.run init
      let simpConfig ←
        if let some stx := config.simpConfigSyntax? then
          if config.options.useSimpAll then
            (·.toConfig) <$> elabSimpConfigCtx stx
          else
            elabSimpConfig stx
        else
          if config.options.useSimpAll then
            pure { : Simp.ConfigCtx}.toConfig
          else
            pure { : Simp.Config }
        return { config with simpConfig }

    addClause (traceScript : Bool) (stx : TSyntax `Aesop.tactic_clause) :
        StateRefT TacticConfig TermElabM Unit :=
      withRef stx do
        match stx with
        | `(tactic_clause| (add $es:Aesop.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run $ .forAdditionalRules goal
          modify λ c => { c with additionalRules := c.additionalRules ++ rs }
        | `(tactic_clause| (erase $es:Aesop.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run $ .forErasing goal
          modify λ c => { c with erasedRules := c.erasedRules ++ rs }
        | `(tactic_clause| (rule_sets := [ $specs:ruleSetSpec,* ])) => do
          let mut enabledRuleSets := (← get).enabledRuleSets
          for spec in (specs : Array Syntax) do
            match spec with
            | `(Parser.ruleSetSpec| - $rsName:ident) => do
              let rsName := RuleSetName.elab rsName
              unless enabledRuleSets.contains rsName do throwError
                "aesop: trying to deactivate rule set '{rsName}', but it is not active"
              enabledRuleSets := enabledRuleSets.erase rsName
            | `(Parser.ruleSetSpec| $rsName:ident) => do
              let rsName := RuleSetName.elab rsName
              if enabledRuleSets.contains rsName then throwError
                "aesop: rule set '{rsName}' is already active"
              enabledRuleSets := enabledRuleSets.insert rsName
            | _ => throwUnsupportedSyntax
          modify λ c => { c with enabledRuleSets }
        | `(tactic_clause| (config := $t:term)) =>
          let options ← elabOptions t
          let options :=
            { options with traceScript := options.traceScript || traceScript }
          modify λ c => { c with options }
        | `(tactic_clause| (simp_config := $t:term)) =>
          modify λ c => { c with simpConfigSyntax? := some t }
        | _ => throwUnsupportedSyntax

def updateRuleSet (rs : LocalRuleSet) (c : TacticConfig) (goal : MVarId):
    TermElabM LocalRuleSet := do
  let mut rs := rs
  for ruleExpr in c.additionalRules do
    let rules ← ruleExpr.buildAdditionalLocalRules goal
    for rule in rules do
      rs := rs.add rule

  -- Erase erased rules
  for ruleExpr in c.erasedRules do
    let filters ← ruleExpr.toLocalRuleFilters |>.run $ .forErasing goal
    for rFilter in filters do
      let (rs', anyErased) := rs.erase rFilter
      rs := rs'
      if ! anyErased then
        throwError "aesop: '{rFilter.name}' is not registered (with the given features) in any rule set."
  return rs

def getRuleSet (goal : MVarId) (c : TacticConfig) :
    TermElabM LocalRuleSet :=
  goal.withContext do
    let rss ← getGlobalRuleSets c.enabledRuleSets.toArray
    c.updateRuleSet (← mkLocalRuleSet rss (← c.options.toOptions')) goal

end Aesop.Frontend.TacticConfig
