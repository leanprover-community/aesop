/-
Copyright (c) 2022-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Nanos
import Aesop.Rule.Name
import Aesop.Tracing

open Lean

namespace Aesop


-- All times are in nanoseconds.
structure RuleStats where
  rule : DisplayRuleName
  elapsed : Nanos
  successful : Bool
  deriving Inhabited

namespace RuleStats

instance : ToString RuleStats where
  toString rp :=
    let success := if rp.successful then "successful" else "failed"
    s!"[{rp.elapsed.printAsMillis}] apply rule {rp.rule} ({success})"

end RuleStats


structure Stats where
  total : Nanos
  configParsing : Nanos
  ruleSetConstruction : Nanos
  search : Nanos
  ruleSelection : Nanos
  ruleStats : Array RuleStats
  deriving Inhabited

namespace Stats

protected def empty : Stats where
  total := 0
  configParsing := 0
  ruleSetConstruction := 0
  search := 0
  ruleSelection := 0
  ruleStats := #[]

instance : EmptyCollection Stats :=
  ⟨Stats.empty⟩

end Stats


structure RuleStatsTotals where
  /--
  Number of successful applications of a rule.
  -/
  numSuccessful : Nat
  /--
  Number of failed applications of a rule.
  -/
  numFailed : Nat
  /--
  Total elapsed time of successful applications of a rule.
  -/
  elapsedSuccessful : Nanos
  /--
  Total elapsed time of failed applications of a rule.
  -/
  elapsedFailed : Nanos

namespace RuleStatsTotals

protected def empty : RuleStatsTotals where
  numSuccessful := 0
  numFailed := 0
  elapsedSuccessful := 0
  elapsedFailed := 0

instance : EmptyCollection RuleStatsTotals :=
  ⟨.empty⟩

def compareByTotalElapsed : (x y : RuleStatsTotals) → Ordering :=
  compareOn λ totals => totals.elapsedSuccessful + totals.elapsedFailed

end RuleStatsTotals


namespace Stats

def ruleStatsTotals (p : Stats)
    (init : HashMap DisplayRuleName RuleStatsTotals := ∅) :
    HashMap DisplayRuleName RuleStatsTotals :=
  p.ruleStats.foldl (init := init) λ m rp => Id.run do
    let mut stats := m.findD rp.rule ∅
    if rp.successful then
      stats := { stats with
        numSuccessful := stats.numSuccessful + 1
        elapsedSuccessful := stats.elapsedSuccessful + rp.elapsed
      }
    else
      stats := { stats with
        numFailed := stats.numFailed + 1
        elapsedFailed := stats.elapsedFailed + rp.elapsed
      }
    m.insert rp.rule stats

def _root_.Aesop.sortRuleStatsTotals
    (ts : Array (DisplayRuleName × RuleStatsTotals)) :
    Array (DisplayRuleName × RuleStatsTotals) :=
  let lt := λ (n₁, t₁) (n₂, t₂) =>
    RuleStatsTotals.compareByTotalElapsed t₁ t₂ |>.swap.then
    (compare n₁ n₂)
    |>.isLT
  ts.qsort lt

def trace (p : Stats) (opt : TraceOption) : CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  let totalRuleApplications :=
    p.ruleStats.foldl (init := 0) λ total rp =>
      total + rp.elapsed
  aesop_trace![opt] "Total: {p.total.printAsMillis}"
  aesop_trace![opt] "Configuration parsing: {p.configParsing.printAsMillis}"
  aesop_trace![opt] "Rule set construction: {p.ruleSetConstruction.printAsMillis}"
  withConstAesopTraceNode opt (collapsed := false)
      (return m!"Search: {p.search.printAsMillis}") do
    aesop_trace![opt] "Rule selection: {p.ruleSelection.printAsMillis}"
    withConstAesopTraceNode opt (collapsed := false)
        (return m!"Rule applications: {totalRuleApplications.printAsMillis}") do
      let timings := sortRuleStatsTotals p.ruleStatsTotals.toArray
      for (n, t) in timings do
        aesop_trace![opt] "[{(t.elapsedSuccessful + t.elapsedFailed).printAsMillis} / {t.elapsedSuccessful.printAsMillis} / {t.elapsedFailed.printAsMillis}] {n}"

end Stats


abbrev StatsRef := IO.Ref Stats

class MonadStats (m) extends
    MonadLiftT (ST IO.RealWorld) m,
    MonadLiftT BaseIO m,
    MonadOptions m where
  readStatsRef : m StatsRef

export MonadStats (readStatsRef)

variable [Monad m] [MonadStats m]

@[inline, always_inline]
def isProfilingEnabled : m Bool :=
  return (← getOptions).getBool `profiler

@[inline, always_inline]
def recordRuleSelectionStats (elapsed : Nanos) : m Unit := do
  (← readStatsRef).modify λ p =>
    { p with ruleSelection := p.ruleSelection + elapsed }

@[inline, always_inline]
def recordRuleStats (rp : RuleStats) : m Unit := do
  (← readStatsRef).modify λ p =>
    { p with ruleStats := p.ruleStats.push rp }

@[inline, always_inline]
def profiling (x : m α) (onlyWhenProfiling : Bool)
    (recordStats : α → Nanos → m Unit) : m α := do
  if ← pure (! onlyWhenProfiling) <||> isProfilingEnabled then
    let (result, elapsed) ← time x
    recordStats result elapsed
    return result
  else
    x

@[inline, always_inline]
def profilingRuleSelection (x : m α) : m α :=
  profiling x (onlyWhenProfiling := false) λ _ elapsed => do
    recordRuleSelectionStats elapsed

@[inline, always_inline]
def profilingRule (rule : DisplayRuleName) (wasSuccessful : α → Bool)
    (x : m α) : m α :=
  profiling x (onlyWhenProfiling := true) λ a elapsed => do
    recordRuleStats { rule, elapsed, successful := wasSuccessful a }

end Aesop
