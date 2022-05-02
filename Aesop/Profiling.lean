/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Nanos
import Aesop.Tree.Data
import Aesop.Tracing

open Lean
open Std (HashMap)

namespace Aesop

inductive RuleProfileName
  | normSimp
  | rule (name : RuleName)
  deriving Inhabited, BEq, Ord

namespace RuleProfileName

instance : ToString RuleProfileName where
  toString
    | rule name => toString name
    | normSimp => "<norm simp>"

instance : Hashable RuleProfileName where
  hash
    | rule name => mixHash (hash name) 4589
    | normSimp => 788009

end RuleProfileName


-- All times are in nanoseconds.
structure RuleProfile where
  rule : RuleProfileName
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
    HashMap RuleProfileName (Nanos × Nanos) := Id.run do
  let mut m := {}
  for rp in p.ruleApplications do
    if rp.successful then
      m := m.insertWith rp.rule (rp.elapsed, 0) λ (successful, failed) =>
        (successful + rp.elapsed, failed)
    else
      m := m.insertWith rp.rule (0, rp.elapsed) λ (successful, failed) =>
        (successful, failed + rp.elapsed)
  return m

open MessageData in
protected def toMessageData (p : Profile) : MessageData :=
  let totalRuleApplications :=
    p.ruleApplications.foldl (init := 0) λ total rp =>
      total + rp.elapsed
  "execution times:" ++ node #[
    m!"total: {p.total.printAsMillis}" ++ node #[
      m!"configuration parsing: {p.configParsing.printAsMillis}",
      m!"rule set construction: {p.ruleSetConstruction.printAsMillis}",
      m!"search: {p.search.printAsMillis}" ++ node #[
        m!"rule selection: {p.ruleSelection.printAsMillis}",
        m!"rule applications: {totalRuleApplications.printAsMillis}" ++
          node (displayRuleApplications p.ruleApplicationTotals)
  ]]]
  where
    compareTimings : (x y : RuleProfileName × Nanos × Nanos) → Ordering :=
      compareOpposite $
        compareLexicographic
          (compareBy (λ (_, s, f) => s + f))
          (compareBy (λ (n, _, _) => n))

    displayRuleApplications (apps : HashMap RuleProfileName (Nanos × Nanos)) :
        Array MessageData := Id.run do
      let mut timings : Array (RuleProfileName × Nanos × Nanos) := #[]
      for (n, (successful, failed)) in apps do
        timings := timings.push (n, successful, failed)
      timings := timings.qsortOrd (ord := ⟨compareTimings⟩)
      let result := timings.map λ (n, s, f) =>
        m!"[{(s + f).printAsMillis} / {s.printAsMillis} / {f.printAsMillis}] {n}"
      return result

instance : ToMessageData Profile :=
  ⟨Profile.toMessageData⟩

end Profile


namespace ProfileT

structure Context where
  isProfilingEnabled : Bool

end ProfileT

abbrev ProfileT m :=
  ReaderT ProfileT.Context $ StateRefT' IO.RealWorld Profile m

namespace ProfileT

protected def run [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : ProfileT m α)
    (isProfilingEnabled : Bool) (profile : Profile) : m (α × Profile) :=
  ReaderT.run x { isProfilingEnabled } |>.run profile

end ProfileT


class abbrev MonadProfile (m : Type → Type _) :=
  MonadReaderOf ProfileT.Context m
  MonadStateOf Profile m

variable [Monad m] [MonadProfile m]

@[inline]
def isProfilingEnabled [MonadProfile m] : m Bool :=
  return (← read).isProfilingEnabled

@[inline]
def recordRuleSelectionProfile (elapsed : Nanos) : m Unit :=
  modify λ p => { p with ruleSelection := p.ruleSelection + elapsed }

@[inline]
def recordRuleProfile (rp :  RuleProfile) : m Unit :=
  modify λ p => { p with ruleApplications := p.ruleApplications.push rp }

@[inline]
def profiling [MonadLiftT BaseIO m] (x : m α)
    (recordProfile : α → Nanos → m Unit) : m α := do
  if ← isProfilingEnabled then
    let (result, elapsed) ← IO.time x
    recordProfile result elapsed
    return result
  else
    x

section

variable [MonadTrace m] [MonadOptions m] [MonadRef m] [AddMessageContext m]

@[inline]
def recordAndTraceRuleSelectionProfile (phase : PhaseName) (elapsed : Nanos) :
    m Unit := do
  aesop_trace[stepsProfile] "[{elapsed.printAsMillis}] {phase} rule selection"
  recordRuleSelectionProfile elapsed

@[inline]
def recordAndTraceRuleProfile (rp : RuleProfile) : m Unit := do
  aesop_trace[stepsProfile] toMessageData rp
  recordRuleProfile rp

end

end Aesop
