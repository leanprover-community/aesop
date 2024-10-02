/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Basic
import Aesop.Stats.Report
import Batteries.Linter.UnreachableTactic
import Aesop.Frontend.Extension
import Aesop.Frontend.RuleExpr

open Lean Lean.Elab Lean.Elab.Command

namespace Aesop.Frontend.Parser

syntax (name := declareRuleSets)
  "declare_aesop_rule_sets " "[" ident,+,? "]"
  ("(" &"default" " := " Aesop.bool_lit ")")? : command

elab_rules : command
  | `(declare_aesop_rule_sets [ $ids:ident,* ]
       $[(default := $dflt?:Aesop.bool_lit)]?) => do
    let rsNames := (ids : Array Ident).map (·.getId)
    let dflt := (← dflt?.mapM (elabBoolLit ·)).getD false
    rsNames.forM checkRuleSetNotDeclared
    elabCommand $ ← `(initialize ($(quote rsNames).forM $ declareRuleSetUnchecked (isDefault := $(quote dflt))))

elab (name := addRules)
    attrKind:attrKind "add_aesop_rules " e:Aesop.rule_expr : command => do
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

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addRules

elab (name := eraseRules)
    "erase_aesop_rules " "[" es:Aesop.rule_expr,* "]" : command => do
  let filters ← Elab.Command.liftTermElabM do
    let ctx ← ElabM.Context.forGlobalErasing
    (es : Array _).mapM λ e => do
      let e ← RuleExpr.elab e |>.run ctx
      e.toGlobalRuleFilters
  for fs in filters do
    for (rsFilter, rFilter) in fs do
      eraseGlobalRules rsFilter rFilter (checkExists := true)

syntax (name := showRules)
  withPosition("#aesop_rules" (colGt ppSpace ident)*) : command

elab_rules : command
  | `(#aesop_rules $ns:ident*) => do
    liftTermElabM do
      let lt := λ (n₁, _) (n₂, _) => n₁.cmp n₂ |>.isLT
      let rss ←
        if ns.isEmpty then
          let rss ← getDeclaredGlobalRuleSets
          pure $ rss.qsort lt
        else
          ns.mapM λ n => return (n.getId, ← getGlobalRuleSet n.getId)
      TraceOption.ruleSet.withEnabled do
        for (name, rs, _) in rss do
          withConstAesopTraceNode .ruleSet (return m!"Rule set '{name}'") do
            rs.trace .ruleSet

def evalStatsReport? (name : Name) : CoreM (Option StatsReport) := do
  try
    unsafe evalConstCheck StatsReport ``StatsReport name
  catch _ =>
    return none

syntax (name := showStats) withPosition("#aesop_stats " (colGt ident)?) : command

elab_rules : command
  | `(#aesop_stats) => do
    logInfo $ StatsReport.default $ ← getStatsArray
  | `(#aesop_stats $report:ident) => do
    let openDecl := OpenDecl.simple ``Aesop.StatsReport []
    withScope (λ s => { s with openDecls := openDecl :: s.openDecls }) do
      let names ← resolveGlobalConst report
      liftTermElabM do
        for name in names do
          if let some report ← evalStatsReport? name then
            logInfo $ report $ ← getStatsArray
            break
        throwError "'{report}' is not a constant of type 'Aesop.StatsReport'"

end Aesop.Frontend.Parser
