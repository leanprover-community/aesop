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

variable {α} [Ord α] [Hashable α]

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

@[specialize]
def applicableByTargetRules (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (IndexMatchResult α)) := do
  let rs ← ri.byTarget.getMatch (← getMVarType goal)
  return rs.map λ r =>
    { rule := r, matchLocations := #[IndexMatchLocation.target] }

@[specialize]
def applicableByHypRules (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (Array (IndexMatchResult α))) :=
  withMVarContext goal do
    let mut rulesList := #[]
    for localDecl in ← getLCtx do
      if localDecl.isAuxDecl then continue
      let rules ← ri.byHyp.getMatch localDecl.type
      let rules := rules.map λ r =>
        { rule := r, matchLocations := #[IndexMatchLocation.hyp localDecl] }
      rulesList := rulesList.push rules
    return rulesList

-- Returns the rules in the order given by `cmp` (which can be different from
-- the order given by `Ord α`).
@[specialize]
def applicableRules (cmp : α → α → Ordering) (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (IndexMatchResult α)) := do
  instantiateMVarsInGoal goal
  let byTarget ← applicableByTargetRules ri goal
  let unindexed : Array (IndexMatchResult α) :=
    ri.unindexed.fold (init := Array.mkEmpty ri.unindexed.size) λ ary r =>
      ary.push { rule := r, matchLocations := #[IndexMatchLocation.none] }
  let byHyp ← applicableByHypRules ri goal
  let mut result := mkRBMap α (Array IndexMatchLocation) cmp
  result := insertIndexMatchResults result byTarget
  result := insertIndexMatchResults result unindexed
  for rs in byHyp do
    result := insertIndexMatchResults result rs
  return result.fold (init := #[]) λ rs rule locs => rs.push
    { rule := rule, matchLocations := locs }
  where
    @[inline]
    insertIndexMatchResults (m : RBMap α (Array IndexMatchLocation) cmp)
        (rs : Array (IndexMatchResult α)) :
        RBMap α (Array IndexMatchLocation) cmp := Id.run do
      let mut result := m
      for r in rs do
        result := result.insertWith r.rule r.matchLocations
          (· ++ r.matchLocations)
      return result

end Aesop.RuleIndex
