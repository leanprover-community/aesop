/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.BestFirstSearch
import Aesop.Config
import Aesop.DefaultRules
import Lean.Elab.Tactic

namespace Aesop

open Lean.Elab.Tactic

@[tactic Parser.Tactic.aesop]
def evalAesop : Tactic := λ stx =>
  withMainContext do
    let config ← TacticConfig.parse stx
    let rs ← getRuleSet
    let rs := rs.addArray (← defaultRules)
    let rs := rs.addArray (← config.additionalRuleSetMembers)
    trace[Aesop.RuleSet] m!"{rs}"
    searchTactic rs

end Aesop
