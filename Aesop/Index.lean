/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
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
    let rules ← ri.byTarget.getUnify (← goal.getType) discrTreeConfig
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
      let rules ← ri.byHyp.getUnify localDecl.type discrTreeConfig
      for r in rules do
        if include? r then
          rs := rs.push (r, #[.hyp localDecl])
    return rs

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableUnindexedRules (ri : Index α) (include? : Rule α → Bool) :
    Array (Rule α × Array IndexMatchLocation) :=
  -- Assumption: include? is true for most rules.
  ri.unindexed.fold (init := #[]) λ acc r =>
    if include? r then
      acc.push (r, #[.none])
    else
      acc

-- Returns the rules in the order given by the `Ord α` instance.
@[specialize]
def applicableRules (ri : Index α) (goal : MVarId)
    (include? : Rule α → Bool) :
    MetaM (Array (IndexMatchResult (Rule α))) := do
  withConstAesopTraceNode .debug (return "rule selection") do
  goal.instantiateMVars
  let mut result :=
    mkRBMap (Rule α) (Array IndexMatchLocation) Rule.compareByPriorityThenName
  result := insertIndexMatchResults result
    (← applicableByTargetRules ri goal include?)
  result := insertIndexMatchResults result
    (← applicableByHypRules ri goal include?)
  result := insertIndexMatchResults result
    (applicableUnindexedRules ri include?)
  aesop_trace[debug] "selected rules before pattern check:{indentD $ flip MessageData.joinSep "\n" $ result.toList.map (toMessageData ·.fst.name)}"
  let patterns :=
    result.fold (init := Array.mkEmpty result.size) λ pats rule _ =>
      if let some pattern := rule.pattern? then
        pats.push (rule.name, pattern)
      else
        pats
  aesop_trace[debug] "patterns:{indentD $ flip MessageData.joinSep "\n" $ patterns.map (λ (name, pat) => m!"{name}: {pat.pattern.expr}") |>.toList}"
  let patternInstsMap ← matchRulePatterns patterns goal
  aesop_trace[debug] "found pattern instantiations:{indentD $ flip MessageData.joinSep "\n" $ patternInstsMap.toList.map λ (name, insts) => m!"{name}: {insts.toArray.map (·.toArray)}"}"
  return result.fold (init := Array.mkEmpty result.size) λ rs rule locs =>
    let_fun locations := (∅ : Std.HashSet _).insertMany locs
    if rule.pattern?.isSome then
      if let some patternInstantiations := patternInstsMap[rule.name]? then
        rs.push { rule, locations, patternInstantiations }
      else
        rs
    else
      rs.push { rule, locations, patternInstantiations := ∅ }
  where
    @[inline]
    insertIndexMatchResults
        (m : RBMap (Rule α) (Array IndexMatchLocation) Rule.compareByPriorityThenName)
        (rs : Array (Rule α × Array IndexMatchLocation)) :
        RBMap (Rule α) (Array IndexMatchLocation) Rule.compareByPriorityThenName :=
      rs.foldl (init := m) λ m (rule, locs) =>
        match m.find? rule with
        | none => m.insert rule locs
        | some locs' => m.insert rule (locs' ++ locs)

end Aesop.Index
