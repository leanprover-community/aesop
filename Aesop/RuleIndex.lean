/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic

open Lean
open Lean.Meta
open Std (RBMap mkRBMap)

namespace Aesop

structure RuleIndex (α : Type) where
  byTarget : DiscrTree α
  byHyp : DiscrTree α
  unindexed : Array α
  deriving Inhabited

namespace RuleIndex

open MessageData in
instance [ToMessageData α] : ToMessageData (RuleIndex α) where
  toMessageData ri := node #[
    "indexed by target:" ++ node (ri.byTarget.values.map toMessageData),
    "indexed by hypotheses:" ++ node (ri.byHyp.values.map toMessageData),
    "unindexed:" ++ node (ri.unindexed.map toMessageData)
    ]

def empty : RuleIndex α where
  byTarget := DiscrTree.empty
  byHyp := DiscrTree.empty
  unindexed := #[]

instance : EmptyCollection (RuleIndex α) :=
  ⟨empty⟩

@[specialize]
def add [BEq α] (r : α) (imode : IndexingMode) (ri : RuleIndex α) :
    RuleIndex α :=
  match imode with
  | IndexingMode.unindexed => { ri with unindexed := ri.unindexed.push r }
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

@[specialize]
def applicableRules [Ord α] (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (IndexMatchResult α)) := do
  instantiateMVarsInGoal goal
  let byTarget ← applicableByTargetRules ri goal
  let unindexed : Array (IndexMatchResult α) := ri.unindexed.map λ r =>
    { rule := r, matchLocations := #[IndexMatchLocation.none] }
  let byHyp ← applicableByHypRules ri goal
  let mut result := mkRBMap α (Array IndexMatchLocation) compare
  result := insertIndexMatchResults result byTarget
  result := insertIndexMatchResults result unindexed
  for rs in byHyp do
    result := insertIndexMatchResults result rs
  return result.fold (init := #[]) λ rs rule locs => rs.push
    { rule := rule, matchLocations := locs }
  where
    @[inline]
    insertIndexMatchResults (m : RBMap α (Array IndexMatchLocation) compare)
        (rs : Array (IndexMatchResult α)) :
        RBMap α (Array IndexMatchLocation) compare := do
      let mut result := m
      for r in rs do
        result := result.insertWith r.rule r.matchLocations
          (· ++ r.matchLocations)
      return result

end Aesop.RuleIndex
