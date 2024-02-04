/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.Frontend.Basic

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

elab "erase_aesop_rules " "[" es:Aesop.rule_expr,* "]" : command => do
  let filters ← (es : Array _).mapM λ e => do
    let e ← Elab.Command.liftTermElabM $
      RuleExpr.elab e |>.run ElabOptions.forErasing
    e.toGlobalRuleNameFilters
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

end Aesop.Frontend.Parser
