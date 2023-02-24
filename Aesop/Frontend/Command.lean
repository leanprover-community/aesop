/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean

namespace Aesop.Frontend.Parser

open Elab.Command in
elab "declare_aesop_rule_sets" "[" ids:ident,+,? "]" : command => do
  let rsNames := (ids : Array Ident).map (·.getId)
  rsNames.forM checkRuleSetNotDeclared
  elabCommand $ ← `(initialize ($(quote rsNames).forM declareRuleSetUnchecked))

elab "erase_aesop_rules" "[" es:Aesop.rule_expr,* "]" : command => do
  let filters ← (es : Array _).mapM λ e => do
    let e ← Elab.Command.liftTermElabM $
      RuleExpr.elab e |>.run ElabOptions.forErasing
    e.toGlobalRuleNameFilters
  for fs in filters do
    for (rsFilter, rFilter) in fs do
      eraseRules rsFilter rFilter (check := true)

elab "#aesop_rules" : command => do
  let rss ← Elab.Command.liftTermElabM do
    getAllRuleSets (includeGlobalSimpTheorems := true)
  logInfo $ toMessageData rss

end Aesop.Frontend.Parser
