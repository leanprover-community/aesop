/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Nanos
import Aesop.Tree.Data
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


-- All times are in nanoseconds.
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

-- The returned map associates to each rule the total time spent on successful
-- and failed applications of that rule.
def ruleStatsTotals (p : Stats) :
    HashMap DisplayRuleName (Nanos × Nanos) := Id.run do
  let mut m := {}
  for rp in p.ruleStats do
    if rp.successful then
      m :=
        match m.find? rp.rule with
        | none => m.insert rp.rule (rp.elapsed, 0)
        | some (successful, failed) =>
          m.insert rp.rule (successful + rp.elapsed, failed)
    else
      m :=
        match m.find? rp.rule with
        | none => m.insert rp.rule (0, rp.elapsed)
        | some (successful, failed) =>
          m.insert rp.rule (successful, failed + rp.elapsed)
  return m

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
      let timings :=
        p.ruleStatsTotals.fold
          (init := Array.mkEmpty p.ruleStatsTotals.size)
          λ timings n (successful, failed) =>
            timings.push (n, successful, failed)
      let timings := timings.qsortOrd (ord := ⟨compareTimings⟩)
      for (n, s, f) in timings do
        aesop_trace![opt] "[{(s + f).printAsMillis} / {s.printAsMillis} / {f.printAsMillis}] {n}"
  where
    compareTimings (x y : DisplayRuleName × Nanos × Nanos) : Ordering :=
      compareLex
        (compareOn (λ (_, s, f) => s + f))
        (compareOn (λ (n, _, _) => n))
        x y
      |>.swap

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
def profiling (x : m α) (recordStats : α → Nanos → m Unit) : m α := do
  if ← isProfilingEnabled then
    let (result, elapsed) ← time x
    recordStats result elapsed
    return result
  else
    x

@[inline, always_inline]
def profilingRuleSelection (x : m α) : m α :=
  profiling x λ _ elapsed => do recordRuleSelectionStats elapsed

@[inline, always_inline]
def profilingRule (rule : DisplayRuleName) (wasSuccessful : α → Bool)
    (x : m α) : m α :=
  profiling x λ a elapsed => do
    recordRuleStats { rule, elapsed, successful := wasSuccessful a }

end Aesop
