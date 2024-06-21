/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.Frontend.Basic
import Aesop.Stats.Report

open Lean Lean.Elab Lean.Elab.Command

namespace Aesop.Frontend.Parser

syntax (name := declareAesopRuleSets)
  "declare_aesop_rule_sets " "[" ident,+,? "]"
  ("(" &"default" " := " Aesop.bool_lit ")")? : command

@[command_elab declareAesopRuleSets]
def elabDeclareAesopRuleSets : CommandElab
  | `(command| declare_aesop_rule_sets [ $ids:ident,* ]
               $[(default := $dflt?:Aesop.bool_lit)]?) => do
    let rsNames := (ids : Array Ident).map (·.getId)
    let dflt := (← dflt?.mapM (elabBoolLit ·)).getD false
    rsNames.forM checkRuleSetNotDeclared
    elabCommand $ ← `(initialize ($(quote rsNames).forM $ declareRuleSetUnchecked (isDefault := $(quote dflt))))
  | _ => throwUnsupportedSyntax

elab attrKind:attrKind "add_aesop_rules " e:Aesop.rule_expr : command => do
  let attrKind :=
    match attrKind with
    | `(Lean.Parser.Term.attrKind| local) => .local
    | `(Lean.Parser.Term.attrKind| scoped) => .scoped
    | _ => .global
  let rules ← liftTermElabM do
    let e ← RuleExpr.elab e |>.run (← ElabM.Context.forAdditionalGlobalRules)
    e.buildAdditionalGlobalRules none
  for (rule, rsNames) in rules do
    for rsName in rsNames do
      addGlobalRule rsName rule attrKind (checkNotExists := true)

elab "erase_aesop_rules " "[" es:Aesop.rule_expr,* "]" : command => do
  let filters ← Elab.Command.liftTermElabM do
    let ctx ← ElabM.Context.forGlobalErasing
    (es : Array _).mapM λ e => do
      let e ← RuleExpr.elab e |>.run ctx
      e.toGlobalRuleFilters
  for fs in filters do
    for (rsFilter, rFilter) in fs do
      eraseGlobalRules rsFilter rFilter (checkExists := true)

elab "#aesop_rules" : command => do
  liftTermElabM do
    let lt := λ (n₁, _) (n₂, _) => n₁.cmp n₂ |>.isLT
    let rss := (← getDeclaredGlobalRuleSets).qsort lt
    TraceOption.ruleSet.withEnabled do
      for (name, rs, _) in rss do
        withConstAesopTraceNode .ruleSet (return m!"Rule set '{name}'") do
          rs.trace .ruleSet

def evalStatsReport? (name : Name) : CoreM (Option StatsReport) := do
  try
    unsafe evalConstCheck StatsReport ``StatsReport name
  catch _ =>
    return none

elab "#aesop_stats" report?:(ident)? : command => do
  let resolveReport : Option Ident → CommandElabM StatsReport
    | none => pure StatsReport.default
    | some id => do
      let openDecl := OpenDecl.simple ``Aesop.StatsReport []
      withScope (λ s => { s with openDecls := openDecl :: s.openDecls }) do
        let names ← resolveGlobalConst id
        liftTermElabM do
          for name in names do
            if let some report ← evalStatsReport? name then
              return report
          throwError "'{id}' is not a constant of type 'Aesop.StatsReport'"
  let report ← resolveReport report?
  logInfo $ report $ ← getStatsArray

end Aesop.Frontend.Parser
