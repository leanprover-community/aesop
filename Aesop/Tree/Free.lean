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
    (dummyRappRef : RappRef)

  private partial def freeGoalRef (gref : GoalRef) : BaseIO Unit := do
    gref.modify λ g => g.setParent dummyMVarClusterRef
    (← gref.get).children.forM freeRappRef

  private partial def freeRappRef (rref : RappRef) : BaseIO Unit := do
    rref.modify λ r => r.setParent dummyGoalRef
    (← rref.get).children.forM freeMVarClusterRef

  private partial def freeMVarClusterRef (cref : MVarClusterRef) :
      BaseIO Unit := do
    cref.modify λ c => c.setParent dummyRappRef
    (← cref.get).goals.forM freeGoalRef
end

private def mkDummyRefs : BaseIO (GoalRef × MVarClusterRef × RappRef) := do
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
    originalGoalId? := default
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
    branchState := default
    failedRapps := default
  }
  let rref ← IO.mkRef $ Rapp.mk {
    id := default
    parent := gref
    children := default
    state := default
    isIrrelevant := default
    appliedRule := default
    successProbability := default
    metaState := default
    introducedMVars := default
    assignedMVars := default
  }
  return (gref, cref, rref)

def GoalRef.free (gref : GoalRef) : BaseIO Unit := do
  let (dgref, dcref, drref) ← mkDummyRefs
  freeGoalRef dgref dcref drref gref

def RappRef.free (rref : RappRef) : BaseIO Unit := do
  let (dgref, dcref, drref) ← mkDummyRefs
  freeRappRef dgref dcref drref rref

def MVarClusterRef.free (cref : MVarClusterRef) : BaseIO Unit := do
  let (dgref, dcref, drref) ← mkDummyRefs
  freeMVarClusterRef dgref dcref drref cref

def freeTree : TreeM Unit := do
  (← get).root.free

end Aesop
