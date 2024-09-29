/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Index.Basic
import Aesop.Util.Basic
import Aesop.Util.UnionFind
import Batteries.Lean.HashSet

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- A slot represents a maximal premise of a forward rule, i.e. a premise with
no forward dependencies. The goal of forward reasoning is to assign a
hypothesis to each slot in such a way that the assignments agree on all
variables shared between them. -/
structure Slot where
  /-- Discrimination tree keys for the type of this slot. -/
  typeDiscrTreeKeys : Array DiscrTree.Key
  /-- Index of the slot. Slots are always part of a list of slots, and `index`
  is the 0-based index of this slot in that list. -/
  index : SlotIndex
  /-- The previous premises that the premise of this slot depends on. -/
  deps : Std.HashSet PremiseIndex
  /-- Common variables shared between this slot and the previous slots. -/
  common : Std.HashSet PremiseIndex
  /-- 0-based index of the premise represented by this slot in the rule type.
  Note that the slots array may use a different ordering than the original
  order of premises, so we *don't* always have `slotIndex ≤ premiseIndex`. -/
  premiseIndex : PremiseIndex
  deriving Inhabited

local instance : BEq Slot :=
  ⟨λ s₁ s₂ => s₁.premiseIndex == s₂.premiseIndex⟩

local instance : Hashable Slot :=
  ⟨(hash ·.premiseIndex)⟩

/-- Information about the decomposed type of a forward rule. -/
structure ForwardRuleInfo where
  /-- Metavariable context in which `premises` and `slotClusters` are valid. -/
  mctx : MetavarContext
  /-- Metavariables representing the premises of the forward rule. -/
  premises : Array MVarId
  /-- Slots representing the maximal premises of the forward rule, partitioned
  into metavariable clusters. -/
  slotClusters : Array (Array Slot)
  deriving Inhabited

namespace ForwardRuleInfo

/-- Construct a `ForwardRuleInfo` for the theorem `thm`. -/
def ofExpr (thm : Expr) : MetaM ForwardRuleInfo := withNewMCtxDepth do
  let e ← inferType thm
  let (premises, _, _) ← forallMetaTelescope e
  let mctx ← getMCtx
  let premises := premises.map (·.mvarId!)
  let mut premiseToIdx : Std.HashMap MVarId PremiseIndex := ∅
  for h : i in [:premises.size] do
    premiseToIdx := premiseToIdx.insert premises[i] ⟨i⟩
  let mut slots : Array Slot := Array.mkEmpty premises.size
  let mut allDeps : Std.HashSet PremiseIndex := ∅
  for h : i in [:premises.size] do
    let mvarId := premises[i]
    let type ← mvarId.getType
    let typeDiscrTreeKeys ← DiscrTree.mkPath type discrTreeConfig
    let mut deps : Std.HashSet PremiseIndex := ∅
    for mvarId in ← getMVars type do
      if let some idx := premiseToIdx[mvarId]? then
        deps := deps.insert idx
    -- We update `index` and `common` with correct info later.
    slots := slots.push {
      index := ⟨0⟩
      premiseIndex := ⟨i⟩
      common := ∅
      deps, typeDiscrTreeKeys
    }
    allDeps := allDeps.insertMany deps
  -- Slots are created only for premises which are maximal, i.e. which do not
  -- appear in any other premises.
  slots := slots.filter (! allDeps.contains ·.premiseIndex)
  -- Slots are clustered into metavariable clusters and sorted as indicated
  -- below.
  let slotClusters := cluster (·.deps.toArray) slots |>.map sortSlots
  -- The sorting ensures that for each slot in a cluster (except the first), the
  -- slot has some variables in common with the previous slots.
  assert! ! slotClusters.any λ cluster => cluster.any λ slot =>
    slot.index.toNat > 0 && slot.common.isEmpty
  return { premises, slotClusters, mctx }
where
  /-- Sort slots such that each slot has at least one variable in common with
  the previous slots. -/
  sortSlots (slots : Array Slot) : Array Slot := Id.run do
    if slots.isEmpty then
      panic! "empty slot cluster"
    have : Ord Slot := ⟨compareOn (·.deps.size)⟩
    let firstSlot := slots.maxI
    let mut newSlots := Array.mkEmpty slots.size |>.push firstSlot
    let mut seen := (∅ : Std.HashSet Slot).insert firstSlot
    let mut previousDeps : Std.HashSet PremiseIndex := firstSlot.deps
    let mut i := 1
    while newSlots.size != slots.size do
      let slot? :=
        slots.find? λ slot =>
          ! seen.contains slot && slot.deps.any (previousDeps.contains ·)
      let some slot := slot?
        | panic! "not enough suitable slots"
      let common := previousDeps.filter (slot.deps.contains ·)
      newSlots := newSlots.push { slot with index := ⟨i⟩, common }
      seen := seen.insert slot
      previousDeps := previousDeps.insertMany slot.deps
      i := i + 1
    return newSlots

end ForwardRuleInfo
