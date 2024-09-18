/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic
import Aesop.Util.EqualUpToIds
import Batteries.Lean.Meta.SavedState

open Lean Std Lean.Meta

namespace Aesop.Script

-- Without {α β : Type} universe inference goes haywire.
@[specialize]
def findFirstStep? {α β : Type} (goals : Array α) (step? : α → Option β)
     (stepOrder : β → Nat) : Option (Nat × α × β) := Id.run do
  let mut firstStep? := none
  for h : pos in [:goals.size] do
    let g := goals[pos]'h.2
    if let some step := step? g then
      if let some (_, _, currentFirstStep) := firstStep? then
        if stepOrder step < stepOrder currentFirstStep then
          firstStep? := some (pos, g, step)
      else
        firstStep? := some (pos, g, step)
    else
      continue
  return firstStep?

def matchGoals (postState₁ postState₂ : Meta.SavedState)
    (goals₁ goals₂ : Array MVarId) : MetaM (Option (Std.HashMap MVarId MVarId)) := do
  let goals₁ ← getProperGoals postState₁ goals₁
  let goals₂ ← getProperGoals postState₂ goals₂
  let (equal, s) ←
    tacticStatesEqualUpToIds' none postState₁.meta.mctx
      postState₂.meta.mctx goals₁ goals₂ (allowAssignmentDiff := true)
  if ! equal then
    return none
  else
    return s.equalMVarIds
where
  getProperGoals (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM (Array MVarId) :=
    state.runMetaM' do
      let (properGoals, _) ← partitionGoalsAndMVars goals
      return properGoals.map (·.fst)

end Aesop.Script
