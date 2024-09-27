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

open Lean Lean.Meta

namespace Aesop

structure Slot where
  /-- Metavariable representing the premise of this slot. -/
  mvarId : MVarId
  /-- Discrimination tree keys for the type of `mvarId`. -/
  typeDiscrTreeKeys : Array DiscrTree.Key
  /-- Index of the slot. Slots are always part of a list of slots, and `index`
  is the 0-based index of this slot in that list. -/
  index : SlotIndex
  /-- The previous premises that the premise of this slot depends on. -/
  deps : Std.HashSet MVarId
  /-- Common variables shared between this slot and the previous slots. -/
  common : Std.HashSet MVarId
  /-- 0-based index of the premise represented by this slot in the rule type.
  Note that the slots array may use a different ordering than the original
  order of premises, so we *don't* always have `slotIndex ≤ premiseIndex`. -/
  premiseIndex : PremiseIndex
  deriving Inhabited

local instance : BEq Slot :=
  ⟨λ s₁ s₂ => s₁.premiseIndex == s₂.premiseIndex⟩

local instance : Hashable Slot :=
  ⟨(hash ·.premiseIndex)⟩

structure ForwardRuleInfo where
  mctx : MetavarContext
  premises : Array MVarId
  slotClusters : Array (Array Slot)
  deriving Inhabited

namespace ForwardRuleInfo

def numSlots (info : ForwardRuleInfo) : Nat :=
  info.slotClusters.foldl (init := 0) λ n cluster => n + cluster.size

/-- Construct a `ForwardRuleInfo` for the theorem `thm`. -/
def ofExpr (thm : Expr) : MetaM ForwardRuleInfo := withNewMCtxDepth do
  let e ← inferType thm
  let (premises, _, _) ← forallMetaTelescope e
  let premises := premises.map (·.mvarId!)
  let mctx ← getMCtx
  let mut slots : Array Slot := Array.mkEmpty premises.size
  let mut previousDeps : Std.HashSet MVarId := ∅
  for h : i in [:premises.size] do
    let mvarId := premises[i]
    let type ← mvarId.getType
    let typeDiscrTreeKeys ← mkDiscrTreePath type
    let deps := (∅ : Std.HashSet _).insertMany $
      (← getMVars type).filter (premises.contains ·)
    let common := deps.filter (previousDeps.contains ·)
    -- We update `index = 0` with correct ordering later (see *)
    slots := slots.push {
      index := ⟨0⟩
      premiseIndex := ⟨i⟩
      mvarId, deps, common, typeDiscrTreeKeys
    }
    previousDeps := previousDeps.insertMany deps
  -- Slots are created only for premises which do not appear in any other
  -- premises.
  slots := slots.filter (! previousDeps.contains ·.mvarId)
  let slotClusters := cluster (·.deps.toArray) slots
  let slotClusters := slotClusters.map λ cluster =>
    cluster.mapIdx λ i slot => { slot with index := ⟨i⟩ }
  -- (*)
  return { premises, slotClusters, mctx }

end ForwardRuleInfo
