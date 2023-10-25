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
structure RuleProfile where
  rule : DisplayRuleName
  elapsed : Nanos
  successful : Bool
  deriving Inhabited

namespace RuleProfile

instance : ToString RuleProfile where
  toString rp :=
    let success := if rp.successful then "successful" else "failed"
    s!"[{rp.elapsed.printAsMillis}] apply rule {rp.rule} ({success})"

end RuleProfile


-- All times are in nanoseconds.
structure Profile where
  total : Nanos
  configParsing : Nanos
  ruleSetConstruction : Nanos
  search : Nanos
  ruleSelection : Nanos
  ruleApplications : Array RuleProfile
  deriving Inhabited

namespace Profile

protected def empty : Profile where
  total := 0
  configParsing := 0
  ruleSetConstruction := 0
  search := 0
  ruleSelection := 0
  ruleApplications := #[]

instance : EmptyCollection Profile :=
  ⟨Profile.empty⟩

-- The returned map associates to each rule the total time spent on successful
-- and failed applications of that rule.
def ruleApplicationTotals (p : Profile) :
    HashMap DisplayRuleName (Nanos × Nanos) := Id.run do
  let mut m := {}
  for rp in p.ruleApplications do
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

def trace (p : Profile) (opt : TraceOption) : CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  let totalRuleApplications :=
    p.ruleApplications.foldl (init := 0) λ total rp =>
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
        p.ruleApplicationTotals.fold
          (init := Array.mkEmpty p.ruleApplicationTotals.size)
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

end Profile


abbrev ProfileT m := StateRefT' IO.RealWorld Profile m

namespace ProfileT

protected def run [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : ProfileT m α)
    (profile : Profile) : m (α × Profile) :=
  StateRefT'.run x profile

-- Can this be expressed in terms of the various monad classes?
def liftBase [MonadLiftT m n] (x : ProfileT m α) : ProfileT n α :=
  λ r => x r

end ProfileT


class abbrev MonadProfile (m : Type → Type _) :=
  MonadOptions m
  MonadStateOf Profile m

variable [Monad m] [MonadProfile m]

@[inline, always_inline]
def isProfilingEnabled [MonadProfile m] : m Bool :=
  return (← getOptions).getBool `profiler

@[inline, always_inline]
def recordRuleSelectionProfile (elapsed : Nanos) : m Unit :=
  modify λ p => { p with ruleSelection := p.ruleSelection + elapsed }

@[inline, always_inline]
def recordRuleProfile (rp : RuleProfile) : m Unit :=
  modify λ p => { p with ruleApplications := p.ruleApplications.push rp }

@[inline, always_inline]
def profiling [MonadLiftT BaseIO m] (x : m α)
    (recordProfile : α → Nanos → m Unit) : m α := do
  if ← isProfilingEnabled then
    let (result, elapsed) ← time x
    recordProfile result elapsed
    return result
  else
    x

end Aesop
