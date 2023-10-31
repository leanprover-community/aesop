/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Tracing
import Std.Lean.Meta.InstantiateMVars

open Lean
open Lean.Meta

namespace Aesop

structure Index (α : Type) [BEq α] [Hashable α] where
  byTarget : DiscrTree α 
  byHyp : DiscrTree α 
  unindexed : PHashSet α
  deriving Inhabited

namespace Index

variable [BEq α] [Hashable α]

def trace [ToString α] (ri : Index α) (traceOpt : TraceOption) :
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
    traceArray (as : Array α) : CoreM Unit :=
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
partial def add (r : α) (imode : IndexingMode) (ri : Index α) :
    Index α :=
  match imode with
  | IndexingMode.unindexed =>
    { ri with unindexed := ri.unindexed.insert r }
  | IndexingMode.target keys =>
    { ri with byTarget := ri.byTarget.insertCore keys r discrTreeConfig }
  | IndexingMode.hyps keys =>
    { ri with byHyp := ri.byHyp.insertCore keys r discrTreeConfig }
  | IndexingMode.or imodes =>
    imodes.foldl (init := ri) λ ri imode =>
      ri.add r imode

def unindex (ri : Index α) (p : α → Bool) : Index α :=
  let (byTarget, unindexed) := filterDiscrTree' ri.unindexed ri.byTarget
  let (byHyp,    unindexed) := filterDiscrTree' unindexed ri.byHyp
  { byTarget, byHyp, unindexed }
  where
    @[inline, always_inline]
    filterDiscrTree' (unindexed : PHashSet α) (t : DiscrTree α) :
        DiscrTree α × PHashSet α :=
      filterDiscrTree (not ∘ p) (λ unindexed v => unindexed.insert v) unindexed
        t

def foldM [Monad m] (ri : Index α) (f : σ → α → m σ) (init : σ) : m σ :=
  match ri with
  | { byHyp, byTarget, unindexed} => do
    let mut s := init
    s ← byHyp.foldValuesM (init := s) f
    s ← byTarget.foldValuesM (init := s) f
    unindexed.foldM (init := s) f

@[inline]
def fold (ri : Index α) (f : σ → α → σ) (init : σ) : σ :=
  Id.run $ ri.foldM (init := init) f

def size : Index α → Nat
  | { byHyp, byTarget, unindexed } =>
    byHyp.size + byTarget.size + unindexed.size

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableByTargetRules (ri : Index α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (α × Array IndexMatchLocation)) :=
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
    (include? : α → Bool) : MetaM (Array (α × Array IndexMatchLocation)) :=
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
private def applicableUnindexedRules (ri : Index α) (include? : α → Bool) :
    Array (α × Array IndexMatchLocation) :=
  -- Assumption: include? is true for most rules.
  ri.unindexed.fold (init := Array.mkEmpty ri.unindexed.size) λ acc r =>
    if include? r then
      acc.push (r, #[.none])
    else
      acc

-- Returns the rules in the order given by the `Ord α` instance.
set_option linter.unusedVariables false in
@[specialize]
def applicableRules [ord : Ord α] (ri : Index α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (IndexMatchResult α)) := do
  goal.instantiateMVars
  let mut result := mkRBMap α (Array IndexMatchLocation) compare
  result := insertIndexMatchResults result
    (← applicableByTargetRules ri goal include?)
  result := insertIndexMatchResults result
    (← applicableByHypRules ri goal include?)
  result := insertIndexMatchResults result
    (applicableUnindexedRules ri include?)
  return result.fold (init := Array.mkEmpty result.size) λ rs rule locs =>
    rs.push { rule := rule, locations := .ofArray locs }
  where
    @[inline]
    insertIndexMatchResults (m : RBMap α (Array IndexMatchLocation) compare)
        (rs : Array (α × Array IndexMatchLocation)) :
        RBMap α (Array IndexMatchLocation) compare :=
      rs.foldl (init := m) λ m (rule, locs) =>
        match m.find? rule with
        | none => m.insert rule locs
        | some locs' => m.insert rule (locs' ++ locs)

end Aesop.Index
