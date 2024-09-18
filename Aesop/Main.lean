/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Main
import Aesop.Frontend.Tactic
import Aesop.Stats.Extension

open Lean
open Lean.Elab.Tactic

namespace Aesop

@[tactic Frontend.Parser.aesopTactic, tactic Frontend.Parser.aesopTactic?]
def evalAesop : Tactic := λ stx => do
  profileitM Exception "aesop" (← getOptions) do
  let goal ← getMainGoal
  goal.withContext do
    let statsRef ← IO.mkRef ∅
    have : MonadStats TacticM := { readStatsRef := return statsRef }
    profiling (λ s _ t => { s with total := t }) do
      let config ← profiling (λ s _ t => { s with configParsing := t }) do
        Frontend.TacticConfig.parse stx goal
      let ruleSet ←
        profiling (λ s _ t => { s with ruleSetConstruction := t }) do
          config.getRuleSet goal
      withConstAesopTraceNode .ruleSet (return "Rule set") do
        ruleSet.trace .ruleSet
      profiling (λ s _ t => { s with search := t }) do
        let (goals, stats) ←
          search goal ruleSet config.options config.simpConfig
            config.simpConfigSyntax? (← statsRef.get)
        replaceMainGoal goals.toList
        statsRef.set stats
    let stats ← statsRef.get
    recordStatsForCurrentFileIfEnabled stx stats
    stats.trace .stats

end Aesop
