/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean

namespace Aesop.Frontend.Parser

syntax "declare_aesop_rule_sets" "[" ident,+,? "]" : command

elab_rules : command
  | `(declare_aesop_rule_sets [ $rsNames:ident,* ]) =>
    (rsNames : Array Syntax).forM (declareRuleSet ·.getId)

elab "erase_aesop_rules" "[" es:Aesop.rule_expr,* "]" : command => do
  let filters ← (es : Array _).mapM λ e => do
    let e ← Elab.Command.liftTermElabM none $
      RuleExpr.elab e |>.run ElabOptions.forErasing
    e.toGlobalRuleNameFilters
  modifyAttributeRuleSets λ rss => do
    let mut rss := rss
    for fs in filters do
      for (rsFilter, rFilter) in fs do
        rss ← rss.eraseRulesChecked rsFilter rFilter
    return rss

elab "#aesop_rules" : command => do
  Elab.logInfo $ toMessageData (← getAttributeRuleSets)

end Aesop.Frontend.Parser
