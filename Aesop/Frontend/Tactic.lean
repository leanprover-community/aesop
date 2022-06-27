/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.Frontend.RuleExpr
import Aesop.Options
import Aesop.Search.Expansion.Simp.Basic

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term

namespace Aesop.Frontend

namespace Parser

declare_syntax_cat Aesop.tactic_clause

syntax ruleSetSpec := "-"? ident

syntax "(" &"add" Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax "(" &"erase" Aesop.rule_expr,+,? ")" : Aesop.tactic_clause
syntax "(" &"rule_sets" "[" ruleSetSpec,+,? "]" ")" : Aesop.tactic_clause
syntax "(" &"options" ":=" term ")" : Aesop.tactic_clause
syntax "(" &"simp_options" ":=" term ")" : Aesop.tactic_clause

syntax (name := aesopTactic) &"aesop" Aesop.tactic_clause* : tactic

end Parser

-- Inspired by declare_config_elab
unsafe def elabConfigUnsafe (type : Name) (stx : Syntax) : TermElabM α :=
  withRef stx do
    let e ← withoutModifyingState <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize do
      let e ← Term.elabTermEnsuringType stx (Lean.mkConst type)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    evalExpr α type e

unsafe def elabOptionsUnsafe : Syntax → TermElabM Aesop.Options :=
  elabConfigUnsafe ``Aesop.Options

@[implementedBy elabOptionsUnsafe]
opaque elabOptions : Syntax → TermElabM Aesop.Options

unsafe def elabSimpConfigUnsafe : Syntax → TermElabM Aesop.SimpConfig :=
  elabConfigUnsafe ``Aesop.SimpConfig

@[implementedBy elabSimpConfigUnsafe]
opaque elabSimpConfig : Syntax → TermElabM Aesop.SimpConfig

structure TacticConfig where
  additionalRules : Array RuleExpr
  erasedRules : Array RuleExpr
  enabledRuleSets : Array RuleSetName
  options : Aesop.Options
  simpConfig : Aesop.SimpConfig

namespace TacticConfig

def parse (stx : Syntax) : TermElabM TacticConfig :=
  withRefThen stx λ
    | `(tactic| aesop $clauses:Aesop.tactic_clause*) =>
      let init := {
        additionalRules := #[]
        erasedRules := #[]
        enabledRuleSets := defaultEnabledRuleSets
        options := {}
        simpConfig := {}
      }
      clauses.foldlM addClause init
    | _ => throwUnsupportedSyntax
  where
    addClause (c : TacticConfig) (stx : Syntax) : TermElabM TacticConfig :=
      withRefThen stx λ
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
              let rsName := rsName.getId
              unless enabledRuleSets.contains rsName do throwError
                "aesop: trying to deactivate rule set '{rsName}', but it is not active"
              enabledRuleSets := enabledRuleSets.erase rsName
            | `(Parser.ruleSetSpec| $rsName:ident) => do
              let rsName := rsName.getId
              if enabledRuleSets.contains rsName then throwError
                "aesop: rule set '{rsName}' is already active"
              enabledRuleSets := enabledRuleSets.push rsName
            | _ => throwUnsupportedSyntax
          return { c with enabledRuleSets }
        | `(tactic_clause| (options := $t:term)) =>
          return { c with options := ← elabOptions t }
        | `(tactic_clause| (simp_options := $t:term)) =>
          return { c with simpConfig := ← elabSimpConfig t }
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
  let ruleSets ← getAttributeRuleSets
  let defaultSimpLemmas ← Meta.getSimpTheorems
  let defaultRuleSet :=
    { ruleSets.default with
      normSimpLemmas :=
        defaultSimpLemmas.merge ruleSets.default.normSimpLemmas }
  let ruleSets := { ruleSets with default := defaultRuleSet }
  let (goal, ruleSets) ← c.updateRuleSets goal ruleSets
  return (goal, ruleSets.makeMergedRuleSet c.enabledRuleSets)

end TacticConfig

end Aesop.Frontend
