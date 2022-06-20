/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tree.Traversal
import Aesop.Tree.TreeM

open Lean
open Lean.Meta
open Std (HashMap HashSet)

namespace Aesop

structure AddGoal where
  goal : MVarId
  mvars : HashSet MVarId
  branchState : BranchState
  deriving Inhabited

structure AddRapp where
  parent : GoalRef
  appliedRule : RegularRule
  successProbability : Percent
  children : Array AddGoal
  metaState : Meta.SavedState
  introducedMVars : HashSet MVarId
  assignedMVars : HashSet MVarId

private def clusterGoals (goals : Array Goal) : Array (Array Goal) := Id.run do
  let mut clusters := UnionFind.ofArray goals
  let mut mvarOccs : HashMap MVarId (Array Goal) := {}
  for g in goals do
    for m in g.mvars do
      match mvarOccs.find? m with
      | some otherOccs =>
        for g' in otherOccs do
          clusters := clusters.merge g g'
        mvarOccs := mvarOccs.insert m (otherOccs.push g)
      | none =>
        mvarOccs := mvarOccs.insert m #[g]
  return clusters.sets.fst

private def findPathForAssignedMVars (assignedMVars : HashSet MVarId)
    (start : GoalRef) : TreeM (Array RappRef × HashSet GoalId) := do
  if assignedMVars.isEmpty then
    return (#[], {})
  let unseen : IO.Ref (HashSet MVarId) ← IO.mkRef assignedMVars
  let pathRapps : IO.Ref (Array RappRef) ← IO.mkRef #[]
  let pathGoals : IO.Ref (HashSet GoalId) ← IO.mkRef {}
  let done ← IO.mkRef false
  preTraverseUp
    (λ gref => do
      let id := (← gref.get).originalGoalId
      pathGoals.modify (·.insert id)
      return true)
    (λ rref => do
      pathRapps.modify (·.push rref)
      for introducedMVar in (← rref.get).introducedMVars do
        unseen.modify (·.erase introducedMVar)
      if (← unseen.get).isEmpty then
        done.set true
        return false
      else
        return true)
    (λ _ =>
      return true)
    (TreeRef.goal start)
  if ! (← done.get) then
    throwError "aesop: internal error: introducing rapps not found for these mvars: {(← unseen.get).toArray}"
  return (← pathRapps.get, ← pathGoals.get)

private def getGoalsToCopy (assignedMVars : HashSet MVarId) (start : GoalRef) :
    TreeM (Array GoalRef) := do
  let (pathRapps, pathGoals) ← findPathForAssignedMVars assignedMVars start
  let mut toCopy := #[]
  let mut toCopyIds := HashSet.empty
  for rref in pathRapps do
    for cref in (← rref.get).children do
      for gref in (← cref.get).goals do
        let g ← gref.get
        let id := g.originalGoalId
        -- We copy goals which
        -- - aren't on the path;
        -- - haven't been copied already;
        -- - contain at least one of the assigned metavariables.
        -- For the first two checks, we identify goals by their
        -- `originalGoalId`, i.e. 'up to copying'.
        if ! pathGoals.contains id && ! toCopyIds.contains id &&
           g.mvars.any (assignedMVars.contains ·) then
          toCopy := toCopy.push gref
          toCopyIds := toCopyIds.insert id
  return toCopy

private unsafe def copyGoals (assignedMVars : HashSet MVarId)
    (parentRef : RappRef) : TreeM (Array Goal) := do
  let parent ← parentRef.get
  let startGoalRef := parent.parent
  let toCopy ← getGoalsToCopy assignedMVars startGoalRef
  toCopy.mapM λ gref => do
    let g ← gref.get
    let mvars ← parent.runMetaM' $
      g.mvars.concatMapM (getMVarsNoDelayed ∘ mkMVar)
    return Goal.mk {
      id := ← getAndIncrementNextGoalId
      parent := unsafeCast () -- will be filled in later
      children := #[]
      originalGoalId? := some g.originalGoalId
      depth := (← parent.depth) + 1
      state := GoalState.unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := g.preNormGoal
      normalizationState := NormalizationState.notNormal
      mvars
      successProbability := parent.successProbability
      addedInIteration := (← read).currentIteration
      lastExpandedInIteration := Iteration.none
      unsafeRulesSelected := false
      unsafeQueue := {}
      branchState := g.branchState
        -- NOTE Copying the branch state gives weird semantics, but I don't
        -- known what else could be reasonably done.
      failedRapps := #[]
    }

private def makeInitialGoal (g : AddGoal)
    (parent : MVarClusterRef) (depth : Nat) (successProbability : Percent) :
    TreeM Goal :=
  return Goal.mk {
    id := ← getAndIncrementNextGoalId
    parent
    children := #[]
    originalGoalId? := none
    depth
    state := GoalState.unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := g.goal
    normalizationState := NormalizationState.notNormal
    mvars := g.mvars.toArray
    successProbability
    addedInIteration := (← read).currentIteration
    lastExpandedInIteration := Iteration.none
    unsafeRulesSelected := false
    unsafeQueue := {}
    branchState := g.branchState
    failedRapps := #[]
  }

private unsafe def addRappUnsafe (r : AddRapp) : TreeM RappRef := do
  -- Construct the new rapp
  let rref : RappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := r.parent
    children := #[] -- will be filled in later
    state := NodeState.unknown
    isIrrelevant := false
    appliedRule := r.appliedRule
    successProbability := r.successProbability
    metaState := r.metaState
    introducedMVars := r.introducedMVars.toArray
    assignedMVars := r.assignedMVars.toArray
  }

  -- Construct the subgoals
  let parentGoal ← r.parent.get
  let goalDepth := parentGoal.depth + 1
  let subgoals : Array Goal ← r.children.mapM
    (makeInitialGoal · (unsafeCast ()) goalDepth r.successProbability)
    -- The parent (`unsafeCast ()`) will be patched up later.

  -- If the rapp assigned any mvars, copy the related goals.
  let copiedGoals : Array Goal ←
    if r.assignedMVars.isEmpty then
      pure #[]
    else
      copyGoals r.assignedMVars rref

  -- If the rapp 'dropped' mvars, add one goal for each dropped mvar. A
  -- dropped mvar is one that appears in the parent of the rapp but not in any
  -- of its subgoals.
  let mut subgoalMVars : HashSet MVarId := {}
  for g in subgoals do
    for m in g.mvars do
      subgoalMVars := subgoalMVars.insert m
  for g in copiedGoals do
    for m in g.mvars do
      subgoalMVars := subgoalMVars.insert m
  let droppedMVars := parentGoal.mvars.filter λ m =>
    ! subgoalMVars.contains m && ! r.assignedMVars.contains m
  let droppedMVarGoals : Array Goal ← droppedMVars.mapM λ goal => do
      let g : AddGoal := {
        goal
        mvars := ← (← rref.get).runMetaM' $ getGoalMVarsNoDelayed goal
        branchState := parentGoal.branchState
      }
      makeInitialGoal g (unsafeCast ()) goalDepth r.successProbability

  let newGoals := subgoals ++ copiedGoals ++ droppedMVarGoals

  -- Construct the new mvar clusters.
  let crefs : Array MVarClusterRef ←
    clusterGoals newGoals |>.mapM λ gs => do
      let grefs ← gs.mapM (IO.mkRef ·)
      let cref ← IO.mkRef $ MVarCluster.mk {
        parent? := some rref
        goals := grefs
        isIrrelevant := false
        state := NodeState.unknown
      }
      -- Patch up information we left out earlier (to break cyclic dependencies).
      grefs.forM λ gref => gref.modify λ g => g.setParent cref
      return cref

  -- Patch up information we left out earlier.
  rref.modify λ r => r.setChildren crefs
  r.parent.modify λ g => g.setChildren $ g.children.push rref

  -- Increment goal and rapp counters.
  incrementNumGoals newGoals.size
  incrementNumRapps
  return rref

-- Adds a new rapp and its subgoals. If the rapp assigns mvars, all relevant
-- goals containing these mvars are copied as children of the rapp as well. Note
-- that adding a rapp may prove the parent goal, but this function does not make
-- the necessary changes. So after calling it, you should check whether the
-- rapp's parent goal is proven and mark it accordingly.
@[implementedBy addRappUnsafe]
opaque addRapp : AddRapp → TreeM RappRef

end Aesop
