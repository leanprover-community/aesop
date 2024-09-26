/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Percent
import Aesop.Stats.Extension

open Lean

namespace Aesop

/-- Assumes that `xs` is ascending. We use a simple nearest-rank definition of
percentiles. -/
def sortedPercentileD (p : Percent) (dflt : α) (xs : Array α) : α :=
  if xs.size == 0 then
    dflt
  else
    let rank := xs.size.toFloat * p.toFloat |>.ceil.toUInt64.toNat |>.min (xs.size - 1)
    xs[rank]?.getD dflt

def sortedMedianD (dflt : α) (xs : Array α) : α :=
  sortedPercentileD ⟨0.5⟩ dflt xs

abbrev StatsReport := StatsArray → Format

namespace StatsReport

local instance : ToString Nanos :=
  ⟨Nanos.printAsMillis⟩

def default : StatsReport := λ statsArray => Id.run do
  let mut total := 0
  let mut configParsing := 0
  let mut ruleSetConstruction := 0
  let mut search := 0
  let mut ruleSelection := 0
  let mut script := 0
  let mut ruleStats : Std.HashMap DisplayRuleName RuleStatsTotals := ∅
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
     Displaying totals and [averages]\n\
     Total Aesop time:      {fmtTime total samples}\n\
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

def scriptsCore (nSlowest := 30) (nontrivialOnly := false) :
    StatsReport := λ statsArray => Id.run do
  let statsArray :=
    if nontrivialOnly then
      statsArray.filter (·.stats.scriptGenerated.isNontrivial)
    else
      statsArray
  let mut staticallyStructured := 0
  let mut perfectlyStaticallyStructured := 0
  let mut dynamicallyStructured := 0
  let mut perfectlyDynamicallyStructured := 0
  let mut totalTimes := Array.mkEmpty statsArray.size
  let mut scriptTimes := Array.mkEmpty statsArray.size
  for stats in statsArray do
    let stats := stats.stats
    totalTimes := totalTimes.push stats.total
    match stats.scriptGenerated with
    | .none => pure ()
    | .staticallyStructured perfect .. =>
      scriptTimes := scriptTimes.push stats.script
      staticallyStructured := staticallyStructured + 1
      if perfect then
        perfectlyStaticallyStructured := perfectlyStaticallyStructured + 1
    | .dynamicallyStructured perfect .. =>
      scriptTimes := scriptTimes.push stats.script
      dynamicallyStructured := dynamicallyStructured + 1
      if perfect then
        perfectlyDynamicallyStructured := perfectlyDynamicallyStructured + 1

  let slowest := statsArray.qsort (λ s₁ s₂ => s₁.stats.script > s₂.stats.script)
  let slowest := slowest[:nSlowest].toArray
  let nSlowest := min slowest.size nSlowest
  let slowestFmt := slowest.map λ e =>
    let pos :=
      match e.position? with
      | some pos => f!"{pos.line}:{pos.column}"
      | none => f!"?:?"
    f!"{e.fileName}:{pos}: script {e.stats.script}, total {e.stats.total}, type {fmtScriptGenerated e.stats.scriptGenerated}"

  f!"Statistics for {statsArray.size} Aesop calls{if nontrivialOnly then f!" with nontrivial script generation" else ""} in current and imported modules\n\
     Total Aesop time:         {fmtTimes totalTimes}\n\
     Script generation time:   {fmtTimes scriptTimes}\n\
     Scripts generated:        {scriptTimes.size}\n\
     - Statically  structured: {staticallyStructured}\n" ++
  f!"  - perfectly:            {perfectlyStaticallyStructured}\n\
     - Dynamically structured: {dynamicallyStructured}\n" ++
  f!"  - perfectly:            {perfectlyDynamicallyStructured}\n\
     \n\
     {nSlowest} Aesop calls with slowest script generation:\n\
     {Format.joinSep slowestFmt.toList "\n"}"
where
  fmtScriptGenerated : ScriptGenerated → Format
    | .none => "<none>"
    | .staticallyStructured perfect _ => f!"static (perfect: {perfect})"
    | .dynamicallyStructured perfect _ => f!"dynamic (perfect: {perfect})"

  fmtTimes (ns : Array Nanos) : Format :=
    let ns := ns.qsortOrd
    let total : Nanos := ns.foldl (init := 0) (· + ·)
    let average := if ns.size == 0 then 0 else total / ns.size
    let min := ns[0]?.getD 0
    let max := ns[ns.size - 1]?.getD 0
    let median := sortedMedianD 0 ns
    let pct80 := sortedPercentileD ⟨0.80⟩ 0 ns
    let pct95 := sortedPercentileD ⟨0.95⟩ 0 ns
    let pct99 := sortedPercentileD ⟨0.99⟩ 0 ns
    f!"{total} (min = {min}, avg = {average}, median = {median}, 80pct = {pct80}, 95pct = {pct95}, 99pct = {pct99}, max = {max})"

def scripts := scriptsCore
def scriptsNontrivial := scriptsCore (nontrivialOnly := true)

end Aesop.StatsReport
