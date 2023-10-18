/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.Frontend.RuleExpr
import Aesop.Options

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term

namespace Aesop.Frontend.Parser

declare_syntax_cat Aesop.tactic_clause

syntax ruleSetSpec := "-"? ident

syntax " (" &"add " Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax " (" &"erase " Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax " (" &"rule_sets " "[" ruleSetSpec,+,? "]" ")" : Aesop.tactic_clause
syntax " (" &"options" " := " term ")" : Aesop.tactic_clause
syntax " (" &"simp_options" " := " term ")" : Aesop.tactic_clause

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
- `(rule_sets [<ruleset>,*])` enables or disables named sets of rules for this
  Aesop call. Example: `(rule_sets [-builtin, MyRuleSet])`.
- `(options { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_options { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. See `Aesop.SimpConfig`.
-/
syntax (name := aesopTactic)  "aesop"  Aesop.tactic_clause* : tactic

@[inherit_doc aesopTactic]
syntax (name := aesopTactic?) "aesop?" Aesop.tactic_clause* : tactic

end Parser

-- Inspired by declare_config_elab
unsafe def elabConfigUnsafe (type : Name) (stx : Syntax) : TermElabM α :=
  withRef stx do
    let e ← withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize <| withoutErrToSorry do
      let e ← Term.elabTermEnsuringType stx (Lean.mkConst type)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    evalExpr' α type e

unsafe def elabOptionsUnsafe : Syntax → TermElabM Aesop.Options :=
  elabConfigUnsafe ``Aesop.Options

@[implemented_by elabOptionsUnsafe]
opaque elabOptions : Syntax → TermElabM Aesop.Options

unsafe def elabSimpConfigUnsafe : Syntax → TermElabM Aesop.SimpConfig :=
  elabConfigUnsafe ``Aesop.SimpConfig

@[implemented_by elabSimpConfigUnsafe]
opaque elabSimpConfig : Syntax → TermElabM Aesop.SimpConfig

structure TacticConfig where
  additionalRules : Array RuleExpr
  erasedRules : Array RuleExpr
  enabledRuleSets : NameSet
  options : Aesop.Options
  simpConfig : Aesop.SimpConfig
  simpConfigSyntax? : Option Term

namespace TacticConfig

def parse (stx : Syntax) : TermElabM TacticConfig :=
  withRef stx do
    match stx with
    | `(tactic| aesop $clauses:Aesop.tactic_clause*) =>
      clauses.foldlM (addClause false) (← init false)
    | `(tactic| aesop? $clauses:Aesop.tactic_clause*) =>
      clauses.foldlM (addClause true) (← init true)
    | _ => throwUnsupportedSyntax
  where
    init (traceScript : Bool) : CoreM TacticConfig := return {
      additionalRules := #[]
      erasedRules := #[]
      enabledRuleSets := ← getDefaultRuleSetNames
      options := { traceScript }
      simpConfig := {}
      simpConfigSyntax? := none
    }

    addClause (traceScript : Bool) (c : TacticConfig) (stx : Syntax) :
        TermElabM TacticConfig :=
      withRef stx do
        match stx with
        | `(tactic_clause| (add $es:Aesop.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run ElabOptions.forAdditionalRules
          return { c with additionalRules := c.additionalRules ++ rs }
        | `(tactic_clause| (erase $es:Aesop.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run ElabOptions.forErasing
          return { c with erasedRules := c.erasedRules ++ rs }
        | `(tactic_clause| (rule_sets [ $specs:ruleSetSpec,* ])) => do
          let mut enabledRuleSets := c.enabledRuleSets
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
          return { c with enabledRuleSets }
        | `(tactic_clause| (options := $t:term)) =>
          let options ← elabOptions t
          let options :=
            { options with traceScript := options.traceScript || traceScript }
          return { c with options }
        | `(tactic_clause| (simp_options := $t:term)) =>
          return {
            c with
            simpConfig := ← elabSimpConfig t
            simpConfigSyntax? := some t
          }
        | _ => throwUnsupportedSyntax

def updateRuleSets (goal : MVarId) (rss : Aesop.RuleSets) (c : TacticConfig) :
    MetaM (MVarId × Aesop.RuleSets) := do
  let mut rss := rss

  -- Add additional rules
  let mut goal := goal
  for ruleExpr in c.additionalRules do
    let (goal', rules) ← ruleExpr.buildAdditionalLocalRules goal
    goal := goal'
    for (rule, rsNames) in rules do
      for rsName in rsNames do
        rss ← rss.addRuleChecked rsName rule

  -- Erase erased rules
  for ruleExpr in c.erasedRules do
    let filters ← ruleExpr.toLocalRuleNameFilters goal
    for (rsFilter, rFilter) in filters do
      rss ← rss.eraseRulesChecked rsFilter rFilter
  return (goal, rss)

def getRuleSet (goal : MVarId) (c : TacticConfig) :
    MetaM (MVarId × Aesop.RuleSet) := do
  let rss ← getRuleSets c.enabledRuleSets (includeGlobalSimpTheorems := true)
  let (goal, rss) ← c.updateRuleSets goal rss
  return (goal, rss.getMergedRuleSet c.options)

end TacticConfig

end Aesop.Frontend
