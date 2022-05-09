/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic

open Lean
open Lean.Meta
open Std (RBMap mkRBMap PHashSet)

namespace Aesop

structure RuleIndex (α : Type) [BEq α] [Hashable α] where
  byTarget : DiscrTree α
  byHyp : DiscrTree α
  unindexed : PHashSet α
  deriving Inhabited

namespace RuleIndex

variable [BEq α] [Hashable α]

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

@[specialize]
partial def add (r : α) (imode : IndexingMode) (ri : RuleIndex α) :
    RuleIndex α :=
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

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableByTargetRules (ri : RuleIndex α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (α × Array IndexMatchLocation)) :=
  withMVarContext goal do
    let rules ← ri.byTarget.getUnify (← getMVarType goal)
    let mut rs := Array.mkEmpty rules.size
      -- Assumption: include? is true for most rules.
    for r in rules do
      if include? r then
        rs := rs.push (r, #[.target])
    return rs

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableByHypRules (ri : RuleIndex α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (α × Array IndexMatchLocation)) :=
  withMVarContext goal do
    let mut rs := #[]
    for localDecl in ← getLCtx do
      if localDecl.isAuxDecl then continue
      let rules ← ri.byHyp.getUnify localDecl.type
      for r in rules do
        if include? r then
          rs := rs.push (r, #[.hyp localDecl])
    return rs

-- May return duplicate `IndexMatchLocation`s.
@[inline]
private def applicableUnindexedRules (ri : RuleIndex α) (include? : α → Bool) :
    Array (α × Array IndexMatchLocation) :=
  -- Assumption: include? is true for most rules.
  ri.unindexed.fold (init := Array.mkEmpty ri.unindexed.size) λ acc r =>
    if include? r then
      acc.push (r, #[.none])
    else
      acc

-- Returns the rules in the order given by the `Ord α` instance.
@[specialize]
def applicableRules [ord : Ord α] (ri : RuleIndex α) (goal : MVarId)
    (include? : α → Bool) : MetaM (Array (IndexMatchResult α)) := do
  instantiateMVarsInGoal goal
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
        m.insertWith rule locs (· ++ locs)

end Aesop.RuleIndex
