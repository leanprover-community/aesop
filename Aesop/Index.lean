/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.Match
import Aesop.Index.Basic
import Aesop.Index.RulePattern
import Aesop.RulePattern
import Aesop.Rule.Basic
import Aesop.Tracing
import Batteries.Lean.Meta.InstantiateMVars
import Batteries.Lean.PersistentHashSet
import Batteries.Lean.Meta.DiscrTree

open Lean
open Lean.Meta

namespace Aesop

structure Index (α : Type) where
  byTarget : DiscrTree (Rule α)
  byHyp : DiscrTree (Rule α)
  unindexed : PHashSet (Rule α)
  deriving Inhabited

namespace Index

variable [BEq α] [Ord α] [Hashable α]

def trace [ToString (Rule α)] (ri : Index α) (traceOpt : TraceOption) :
    CoreM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  withConstAesopTraceNode traceOpt (return "Indexed by target") do
    traceArray ri.byTarget.values
  withConstAesopTraceNode traceOpt (return "Indexed by hypotheses") do
    traceArray ri.byHyp.values
  withConstAesopTraceNode traceOpt (return "Unindexed") do
    traceArray $ PersistentHashSet.toArray ri.unindexed
  where
    traceArray (as : Array (Rule α)) : CoreM Unit :=
      as.map toString |>.qsortOrd.forM λ r => do aesop_trace![traceOpt] r

instance : EmptyCollection (Index α) where
  emptyCollection := {
    byTarget := {}
    byHyp := {}
    unindexed := {}
  }

def merge (ri₁ ri₂ : Index α) : Index α where
  byTarget := ri₁.byTarget.mergePreservingDuplicates ri₂.byTarget
  byHyp := ri₁.byHyp.mergePreservingDuplicates ri₂.byHyp
  unindexed := ri₁.unindexed.merge ri₂.unindexed

@[specialize]
partial def add (r : Rule α) (imode : IndexingMode) (ri : Index α) :
    Index α :=
  match imode with
  | IndexingMode.unindexed =>
    { ri with unindexed := ri.unindexed.insert r }
  | IndexingMode.target keys =>
    { ri with byTarget := ri.byTarget.insertCore keys r }
  | IndexingMode.hyps keys =>
    { ri with byHyp := ri.byHyp.insertCore keys r }
  | IndexingMode.or imodes =>
    imodes.foldl (init := ri) λ ri imode =>
      ri.add r imode

def unindex (ri : Index α) (p : Rule α → Bool) : Index α :=
  let (byTarget, unindexed) := filterDiscrTree' ri.unindexed ri.byTarget
  let (byHyp,    unindexed) := filterDiscrTree' unindexed ri.byHyp
  { byTarget, byHyp, unindexed }
  where
    @[inline, always_inline]
    filterDiscrTree' (unindexed : PHashSet (Rule α)) (t : DiscrTree (Rule α)) :
        DiscrTree (Rule α) × PHashSet (Rule α) :=
      filterDiscrTree (not ∘ p) (λ unindexed v => unindexed.insert v) unindexed
        t

def foldM [Monad m] (ri : Index α) (f : σ → Rule α → m σ) (init : σ) : m σ :=
  match ri with
  | { byHyp, byTarget, unindexed} => do
    let mut s := init
    s ← byHyp.foldValuesM (init := s) f
    s ← byTarget.foldValuesM (init := s) f
    unindexed.foldM (init := s) f

@[inline]
def fold (ri : Index α) (f : σ → Rule α → σ) (init : σ) : σ :=
  Id.run $ ri.foldM (init := init) f

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableByTargetRules (ri : Index α) (goal : MVarId)
    (include? : Rule α → Bool) :
    MetaM (Array (Rule α × Array IndexMatchLocation)) :=
  goal.withContext do
    let rules ← getUnify ri.byTarget (← goal.getType)
    let mut rs := Array.mkEmpty rules.size
      -- Assumption: include? is true for most rules.
    for r in rules do
      if include? r then
        rs := rs.push (r, #[.target])
    return rs

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableByHypRules (ri : Index α) (goal : MVarId)
    (include? : Rule α → Bool) :
    MetaM (Array (Rule α × Array IndexMatchLocation)) :=
  goal.withContext do
    let mut rs := #[]
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      let rules ← getUnify ri.byHyp localDecl.type
      for r in rules do
        if include? r then
          rs := rs.push (r, #[.hyp localDecl])
    return rs

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableUnindexedRules (ri : Index α) (include? : Rule α → Bool) :
    Array (Rule α × Array IndexMatchLocation) :=
  ri.unindexed.fold (init := #[]) λ acc r =>
    if include? r then
      acc.push (r, #[.none])
    else
      acc

-- Returns the rules in the order given by the `Ord α` instance.
@[specialize]
def applicableRules (ri : Index α) (goal : MVarId)
    (patSubstMap : RulePatternSubstMap)
    (additionalRules : Array (IndexMatchResult (Rule α)))
    (include? : Rule α → Bool) :
    MetaM (Array (IndexMatchResult (Rule α))) := do
  withConstAesopTraceNode .debug (return "rule selection") do
  goal.instantiateMVars
  let result := addRules additionalRules #[
    (← applicableByTargetRules ri goal include?),
    (← applicableByHypRules ri goal include?),
    (applicableUnindexedRules ri include?)
  ]
  let result := result.qsort λ x y => x.rule.compareByPriorityThenName y.rule |>.isLT
  aesop_trace[debug] "selected rules:{.joinSep (result.map (m!"{·.rule.name}") |>.toList) "\n"}"
  return result
where
  addRules (acc : Array (IndexMatchResult (Rule α)))
      (ruless : Array (Array (Rule α × Array IndexMatchLocation))) :
      Array (IndexMatchResult (Rule α)) := Id.run do
    let mut locMap : Std.HashMap (Rule α) (Std.HashSet IndexMatchLocation) := ∅
    for rules in ruless do
      for (rule, locs) in rules do
        if let some locs' := locMap[rule]? then
          locMap := locMap.insert rule (locs'.insertMany locs)
        else
          locMap := locMap.insert rule (.ofArray locs)
    let mut result := acc
    for (rule, locations) in locMap do
      if rule.pattern?.isSome then
        let patternSubsts? := patSubstMap[rule.name]?
        if patternSubsts?.isSome then
          result := result.push { rule, locations, patternSubsts? }
      else
        result := result.push { rule, locations, patternSubsts? := none }
    return result

end Aesop.Index
