/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.BestFirstSearch
import Aesop.BuiltinRules -- ensures that the builtin rules are registered
import Aesop.Config
import Aesop.Profiling
import Lean

open Lean
open Lean.Elab.Tactic

namespace Aesop

@[tactic Parser.Tactic.aesop]
def evalAesop : Tactic := λ stx =>
  withMainContext do
    let (config, configParseTime) ← IO.time $ Config.TacticConfig.parse stx
    let (rs, ruleSetConstructionTime) ← IO.time do
      let rs ←
        Config.getAttributeRuleSet (includeDefaultSimpLemmas := true) -- TODO
          config.enabledRuleSets
      let additionalRuleSetMembers ← liftMetaTacticAux λ goal => do
        let (goal, rs) ← config.buildAdditionalRules goal
        pure (rs, [goal])
      return rs.addArray additionalRuleSetMembers
    aesop_trace[ruleSet] "{rs}"
    let (_, searchTime) ← IO.time $ searchTactic rs config.options
    aesop_trace[profile] toMessageData
      { configParsing := configParseTime
        ruleSetConstruction := ruleSetConstructionTime
        search := searchTime
        : ProfilingTimes }

end Aesop
