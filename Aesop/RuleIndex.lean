/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic

open Lean
open Lean.Meta
open Std (RBMap mkRBMap HashSet)

namespace Aesop

structure RuleIndex (α : Type) [Ord α] [Hashable α] where
  byTarget : DiscrTree α
  byHyp : DiscrTree α
  unindexed : HashSet α
  deriving Inhabited

namespace RuleIndex

variable [Ord α] [Hashable α]

open MessageData in
instance [ToMessageData α] : ToMessageData (RuleIndex α) where
  toMessageData ri := node #[
    "indexed by target:" ++ node (ri.byTarget.values.map toMessageData),
    "indexed by hypotheses:" ++ node (ri.byHyp.values.map toMessageData),
    "unindexed:" ++ node (ri.unindexed.toArray.map toMessageData)
  ]

instance : EmptyCollection (RuleIndex α) where
  emptyCollection := {
    byTarget := {}
    byHyp := {}
    unindexed := {}
  }

def merge (ri₁ ri₂ : RuleIndex α) : RuleIndex α where
  byTarget := ri₁.byTarget.merge ri₂.byTarget
  byHyp := ri₁.byHyp.merge ri₂.byHyp
  unindexed := ri₁.unindexed.merge ri₂.unindexed

instance : Append (RuleIndex α) :=
  ⟨merge⟩

@[specialize]
def add (r : α) (imode : IndexingMode) (ri : RuleIndex α) :
    RuleIndex α :=
  match imode with
  | IndexingMode.unindexed => { ri with unindexed := ri.unindexed.insert r }
  | IndexingMode.target keys =>
    { ri with byTarget := ri.byTarget.insertCore keys r }
  | IndexingMode.hyps keys =>
    { ri with byHyp := ri.byHyp.insertCore keys r }

def foldM [Monad m] (ri : RuleIndex α) (f : σ → α → m σ) (init : σ) : m σ :=
  match ri with
  | { byHyp, byTarget, unindexed} => do
    let mut s := init
    s ← byHyp.foldValuesM (init := s) f
    s ← byTarget.foldValuesM (init := s) f
    unindexed.foldM (init := s) f

@[inline]
def fold (ri : RuleIndex α) (f : σ → α → σ) (init : σ) : σ :=
  Id.run $ ri.foldM (init := init) f

def size : RuleIndex α → Nat
  | { byHyp, byTarget, unindexed } =>
    byHyp.size + byTarget.size + unindexed.size

@[specialize]
def applicableByTargetRules (ri : RuleIndex α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (IndexMatchResult α)) :=
  withMVarContext goal do
    let rules ← ri.byTarget.getMatch (← getMVarType goal) -- TODO `getUnify` instead of `getMatch`?
    return rules.filterMap λ r =>
      if include? r then
        some { rule := r, matchLocations := #[IndexMatchLocation.target] }
      else
        none

@[specialize]
def applicableByHypRules (ri : RuleIndex α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (IndexMatchResult α)) :=
  withMVarContext goal do
    let mut rs := #[]
    for localDecl in ← getLCtx do
      if localDecl.isAuxDecl then continue
      let rules ← ri.byHyp.getMatch localDecl.type
      for r in rules do
        if include? r then
          let r :=
            { rule := r, matchLocations := #[IndexMatchLocation.hyp localDecl] }
          rs := rs.push r
    return rs

@[specialize]
def applicableUnindexedRules (ri : RuleIndex α) (include? : α → Bool) :
    Array (IndexMatchResult α) := Id.run do
  let mut rs := Array.mkEmpty ri.unindexed.size
    -- Assumption: include? is true for most rules.
  for r in ri.unindexed do
    if include? r then
      rs := rs.push { rule := r, matchLocations := #[IndexMatchLocation.none] }
  return rs

-- Returns the rules in the order given by `cmp` (which can be different from
-- the order given by `Ord α`). `cmp` must return `Ordering.eq` only for rules
-- which are really equal.
@[specialize]
def applicableRules (ri : RuleIndex α) (goal : MVarId) (cmp : α → α → Ordering)
    (include? : α → Bool) : MetaM (Array (IndexMatchResult α)) := do
  instantiateMVarsInGoal goal
  let mut result := mkRBMap α (Array IndexMatchLocation) cmp -- TODO avoid RBMap
  result := insertIndexMatchResults result
    (← applicableByTargetRules ri goal include?)
  result := insertIndexMatchResults result
    (← applicableByHypRules ri goal include?)
  result := insertIndexMatchResults result
    (applicableUnindexedRules ri include?)
  return result.fold (init := Array.mkEmpty result.size) λ rs rule locs =>
    rs.push { rule := rule, matchLocations := locs }
  where
    @[inline]
    insertIndexMatchResults (m : RBMap α (Array IndexMatchLocation) cmp)
        (rs : Array (IndexMatchResult α)) :
        RBMap α (Array IndexMatchLocation) cmp :=
      rs.foldl (init := m) λ m r =>
        m.insertWith r.rule r.matchLocations (· ++ r.matchLocations)

end Aesop.RuleIndex
