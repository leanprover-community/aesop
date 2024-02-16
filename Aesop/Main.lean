/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Main
import Aesop.BuiltinRules -- ensures that the builtin rules are registered
import Aesop.Frontend.Tactic
import Aesop.Stats.Extension

open Lean
open Lean.Elab.Tactic

namespace Aesop

@[tactic Frontend.Parser.aesopTactic, tactic Frontend.Parser.aesopTactic?]
def evalAesop : Tactic := λ stx => do
  profileitM Exception "aesop" (← getOptions) do
  withMainContext do
    let (stats, totalTime) ← time do
      let (config, configParseTime) ← time $ Frontend.TacticConfig.parse stx
      let stats := { Stats.empty with configParsing := configParseTime }
      let goal ← getMainGoal
      let ((goal, ruleSet), ruleSetConstructionTime) ← time $
        config.getRuleSet goal
      let stats :=
        { stats with ruleSetConstruction := ruleSetConstructionTime }
      withConstAesopTraceNode .ruleSet (return "Rule set") do
        ruleSet.trace .ruleSet
      let (stats, searchTime) ← time do
        let (goals, stats) ←
          search goal ruleSet config.options config.simpConfig
            config.simpConfigSyntax? stats
        replaceMainGoal goals.toList
        pure stats
      pure { stats with search := searchTime }
    let stats := { stats with total := totalTime }
    recordStats { aesopStx := stx, stats }
    stats.trace .stats

end Aesop
