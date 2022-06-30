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

structure AddRapp where
  parent : GoalRef
  appliedRule : RegularRule
  successProbability : Percent
  goals : Array (MVarId × Array MVarId)
  introducedMVars : HashSet MVarId
  metaState : Meta.SavedState
  branchState : BranchState
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
    throwError "aesop: internal error: introducing rapps not found for these mvars: {(← unseen.get).toArray.map (·.name)}"
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
    (start : GoalRef) (parentMetaState : Meta.SavedState)
    (parentSuccessProbability : Percent) (depth : Nat) :
    TreeM (Array Goal) := do
  let toCopy ← getGoalsToCopy assignedMVars start
  toCopy.mapM λ gref => do
    let g ← gref.get
    let mvars ← parentMetaState.runMetaM' $
      g.mvars.concatMapM (getMVarsNoDelayed ∘ mkMVar)
    return Goal.mk {
      id := ← getAndIncrementNextGoalId
      parent := unsafeCast () -- will be filled in later
      children := #[]
      origin := .copied g.id g.originalGoalId
      depth
      state := GoalState.unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := g.preNormGoal
      normalizationState := NormalizationState.notNormal
      mvars
      successProbability := parentSuccessProbability
      addedInIteration := (← read).currentIteration
      lastExpandedInIteration := Iteration.none
      unsafeRulesSelected := false
      unsafeQueue := {}
      branchState := g.branchState
        -- NOTE Copying the branch state gives weird semantics, but I don't
        -- known what else could be reasonably done.
      failedRapps := #[]
    }

private def makeInitialGoal (goal : MVarId) (mvars : Array MVarId)
    (parent : MVarClusterRef) (depth : Nat) (successProbability : Percent)
    (branchState : BranchState) (origin : GoalOrigin):
    TreeM Goal :=
  return Goal.mk {
    id := ← getAndIncrementNextGoalId
    children := #[]
    state := GoalState.unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := goal
    normalizationState := NormalizationState.notNormal
    addedInIteration := (← read).currentIteration
    lastExpandedInIteration := Iteration.none
    unsafeRulesSelected := false
    unsafeQueue := {}
    failedRapps := #[]
    parent, branchState, origin, depth, mvars, successProbability
  }

private unsafe def addRappUnsafe (r : AddRapp) : TreeM (Option RappRef) := do
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
    introducedMVars := #[] -- will be filled in later
    assignedMVars := r.assignedMVars.toArray
  }

  let mut mvarsInSubgoals : HashSet MVarId := {}

  -- If the rapp assigned any mvars, copy the related goals.
  let parentGoal ← r.parent.get
  let goalDepth := parentGoal.depth + 1
  let copiedGoals : Array Goal ←
    if r.assignedMVars.isEmpty then
      pure #[]
    else
      copyGoals r.assignedMVars r.parent r.metaState r.successProbability
        goalDepth
  for g in copiedGoals do
    mvarsInSubgoals := mvarsInSubgoals.insertMany g.mvars

  -- Check if the rapp 'dropped' mvars. A dropped mvar is one that appears in
  -- the parent of the rapp but not in any of its subgoals.
  let mut subgoalMVars : HashSet MVarId := {}
  for (_, mvars) in r.goals do
    subgoalMVars := subgoalMVars.insertMany mvars
  for g in copiedGoals do
    subgoalMVars := subgoalMVars.insertMany g.mvars
  let hasDroppedMVar := parentGoal.mvars.any λ m =>
    ! subgoalMVars.contains m && ! r.assignedMVars.contains m
  if hasDroppedMVar then
    return none

  -- Turns proper goals into proper mvars if they appear in any of the copied
  -- subgoals.
  let mut properGoals := Array.mkEmpty r.goals.size
  let mut properMVars := r.introducedMVars.toArray
  for (g, mvars) in r.goals do
    if subgoalMVars.contains g then
      properMVars := properMVars.push g
    else
      properGoals := properGoals.push (g, mvars)

  -- Construct the subgoals
  let subgoals : Array Goal ← properGoals.mapM λ (goal, mvars) =>
    makeInitialGoal goal mvars (unsafeCast ()) goalDepth
      r.successProbability r.branchState .subgoal
    -- The parent (`unsafeCast ()`) will be patched up later.

  let newGoals := subgoals ++ copiedGoals

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
  rref.modify λ r =>
    r.setChildren crefs |>.setIntroducedMVars properMVars
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
--
-- If the rapp dropped mvars, it cannot be added and `none` is returned.
@[implementedBy addRappUnsafe]
opaque addRapp : AddRapp → TreeM (Option RappRef)

end Aesop
