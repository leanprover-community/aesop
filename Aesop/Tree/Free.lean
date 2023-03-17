/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tree.TreeM

namespace Aesop

-- In Lean 4, cylic structures -- such as our trees with their parent pointers
-- -- are not freed automatically. This is because the runtime uses reference
-- counting and a parent node and its child, holding references to each other,
-- will always have a reference count ≥ 1. So in order to free a tree, we must
-- break the cycles by removing the parent pointers.

mutual
  variable
    (dummyGoalRef : GoalRef)
    (dummyMVarClusterRef : MVarClusterRef)

  private partial def freeGoalRef (gref : GoalRef) : BaseIO Unit := do
    gref.modify λ g => g.setParent dummyMVarClusterRef
    (← gref.get).children.forM freeRappRef

  private partial def freeRappRef (rref : RappRef) : BaseIO Unit := do
    rref.modify λ r => r.setParent dummyGoalRef
    (← rref.get).children.forM freeMVarClusterRef

  private partial def freeMVarClusterRef (cref : MVarClusterRef) :
      BaseIO Unit := do
    cref.modify λ c => c.setParent none
    (← cref.get).goals.forM freeGoalRef
end

private def mkDummyRefs : BaseIO (GoalRef × MVarClusterRef) := do
  let cref ← IO.mkRef $ MVarCluster.mk {
    parent? := default
    goals := #[]
    isIrrelevant := default
    state := default
  }
  let gref ← IO.mkRef $ Goal.mk {
    id := default
    parent := cref
    children := default
    origin := default
    depth := default
    state := default
    isIrrelevant := default
    isForcedUnprovable := default
    preNormGoal := default
    normalizationState := default
    mvars := default
    successProbability := default
    addedInIteration := default
    lastExpandedInIteration := default
    unsafeRulesSelected := default
    unsafeQueue := default
    failedRapps := default
  }
  return (gref, cref)

def GoalRef.free (gref : GoalRef) : BaseIO Unit := do
  let (dgref, dcref) ← mkDummyRefs
  freeGoalRef dgref dcref gref

def RappRef.free (rref : RappRef) : BaseIO Unit := do
  let (dgref, dcref) ← mkDummyRefs
  freeRappRef dgref dcref rref

def MVarClusterRef.free (cref : MVarClusterRef) : BaseIO Unit := do
  let (dgref, dcref) ← mkDummyRefs
  freeMVarClusterRef dgref dcref cref

def freeTree : TreeM Unit := do
  (← get).root.free

end Aesop
