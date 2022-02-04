/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.BestFirstSearch
import Aesop.BuiltinRules -- ensures that the builtin rules are registered
import Aesop.Config
import Lean

open Lean.Elab.Tactic

namespace Aesop

@[tactic Parser.Tactic.aesop]
def evalAesop : Tactic := λ stx =>
  withMainContext do
    let config ← Config.TacticConfig.parse stx
    let rs ←
      Config.getAttributeRuleSet (includeDefaultSimpLemmas := true) -- TODO
        config.enabledRuleSets
    let additionalRuleSetMembers ← liftMetaTacticAux λ goal => do
      let (goal, rs) ← config.buildAdditionalRules goal
      pure (rs, [goal])
    let rs := rs.addArray additionalRuleSetMembers
    aesop_trace[ruleSet] "{rs}"
    searchTactic rs config.options

end Aesop
