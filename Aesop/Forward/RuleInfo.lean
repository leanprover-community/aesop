/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Index.Basic
import Aesop.Util.Basic
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
  order of premises, so it is *not* the case that `slotIndex ≤ premiseIndex`. -/
  premiseIndex : PremiseIndex
  deriving Inhabited

structure ForwardRuleInfo where
  metaState : Meta.SavedState
  premises : Array MVarId
  slots : Array Slot
  deriving Nonempty

namespace ForwardRuleInfo

/-- Construct a `ForwardRuleInfo` for the theorem `thm`. -/
def ofExpr (thm : Expr) : MetaM ForwardRuleInfo := withNewMCtxDepth do
  let e ← inferType thm
  let (premises, _, _) ← forallMetaTelescope e
  let premises := premises.map (·.mvarId!)
  let metaState ← saveState
  let mut slots := Array.mkEmpty premises.size
  let mut previousDeps := Std.HashSet.empty
  for h : i in [:premises.size] do
    let mvarId := premises[i]
    let type ← mvarId.getType
    let typeDiscrTreeKeys ← mkDiscrTreePath type
    let deps := Std.HashSet.ofArray $
      (← getMVars type).filter (premises.contains ·)
    let common := HashSet.filter deps (previousDeps.contains ·)
    -- We update `index = 0` with correct ordering later (see *)
    slots := slots.push {
      index := ⟨0⟩
      premiseIndex := ⟨i⟩
      mvarId, deps, common, typeDiscrTreeKeys
    }
    previousDeps := previousDeps.insertMany deps
  -- Slots are created only for premises which do not appear in any other
  -- premises.
  slots := slots.filter fun slot => ! previousDeps.contains slot.mvarId
  -- (*)
  slots := slots.mapIdx fun index current => { current with index := ⟨index⟩ }
  return { premises, slots, metaState }

end ForwardRuleInfo
