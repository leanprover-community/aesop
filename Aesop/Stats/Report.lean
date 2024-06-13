/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Stats.Extension

open Lean

namespace Aesop

abbrev StatsReport := StatsArray → Format

namespace StatsReport

local instance : ToString Nanos :=
  ⟨Nanos.printAsMillis⟩

protected def default : StatsReport := λ statsArray => Id.run do
  let mut total := 0
  let mut configParsing := 0
  let mut ruleSetConstruction := 0
  let mut search := 0
  let mut ruleSelection := 0
  let mut script := 0
  let mut ruleStats : HashMap DisplayRuleName RuleStatsTotals := ∅
  for stats in statsArray do
    let stats := stats.stats
    total := total + stats.total
    configParsing := configParsing + stats.configParsing
    ruleSetConstruction := ruleSetConstruction + stats.ruleSetConstruction
    search := search + stats.search
    ruleSelection := ruleSelection + stats.ruleSelection
    script := script + stats.script
    ruleStats := stats.ruleStatsTotals (init := ruleStats)
  let samples := statsArray.size
  f!"Statistics for {statsArray.size} Aesop calls in current and imported modules\n\
     Displaying totals and [averages] in milliseconds\n\
     Total time:            {fmtTime total samples}\n\
     Config parsing:        {fmtTime configParsing samples}\n\
     Rule set construction: {fmtTime ruleSetConstruction samples}\n\
     Rule selection:        {fmtTime ruleSelection samples}\n\
     Script generation:     {fmtTime script samples}\n\
     Search:                {fmtTime search samples}\n\
     Rules:{Std.Format.indentD $ fmtRuleStats $ sortRuleStatsTotals $ ruleStats.toArray}"
where
  fmtTime (n : Nanos) (samples : Nat) : Format :=
    f!"{n} [{if samples == 0 then 0 else n / samples}]"

  fmtRuleStats (stats : Array (DisplayRuleName × RuleStatsTotals)) :
      Format := Id.run do
    let fmtSection (n : Nanos) (samples : Nat) : Format :=
      f!"{samples} in {fmtTime n samples}"
    let mut fmt := f!""
    for (name, totals) in stats do
      fmt := fmt ++
        f!"{name}:\n\
          {"  "}total:      {fmtSection (totals.elapsedSuccessful + totals.elapsedFailed) (totals.numSuccessful + totals.numFailed)}\n\
          {"  "}successful: {fmtSection totals.elapsedSuccessful totals.numSuccessful}\n\
          {"  "}failed:     {fmtSection totals.elapsedFailed totals.numFailed}\n"
    return fmt

end Aesop.StatsReport
