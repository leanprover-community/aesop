/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Forward.State.ApplyGoalDiff
import Aesop.Tree.Traversal
import Aesop.Tree.TreeM
import Aesop.Util.UnionFind

open Lean
open Lean.Meta

namespace Aesop

structure AddRapp extends RuleApplication where
  parent : GoalRef
  appliedRule : RegularRule
  successProbability : Percent

namespace AddRapp

def consumedForwardRuleMatches (r : AddRapp) : Array ForwardRuleMatch :=
  r.appliedRule.tac.forwardRuleMatches? |>.getD #[]

end AddRapp

def findPathForAssignedMVars (assignedMVars : UnorderedArraySet MVarId)
    (start : GoalRef) : TreeM (Array RappRef × Std.HashSet GoalId) := do
  if assignedMVars.isEmpty then
    return (#[], {})
  let unseen : IO.Ref (UnorderedArraySet MVarId) ← IO.mkRef assignedMVars
  let pathRapps : IO.Ref (Array RappRef) ← IO.mkRef #[]
  let pathGoals : IO.Ref (Std.HashSet GoalId) ← IO.mkRef {}
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
        return false
      else
        return true)
    (λ _ =>
      return true)
    (TreeRef.goal start)
  let unseen ← unseen.get
  if ! unseen.isEmpty then
    let rootGoalMVars := (← (← getRootGoal).get).mvars
    if unseen.any (! rootGoalMVars.contains ·) then
      let reallyUnseen :=
        unseen.toArray.filter (! rootGoalMVars.contains ·) |>.map (·.name)
      throwError "aesop: internal error: introducing rapps not found for these mvars: {reallyUnseen}"
  return (← pathRapps.get, ← pathGoals.get)

def getGoalsToCopy (assignedMVars : UnorderedArraySet MVarId)
    (start : GoalRef) : TreeM (Array GoalRef) := do
  let (pathRapps, pathGoals) ← findPathForAssignedMVars assignedMVars start
  let mut toCopy := #[]
  let mut toCopyIds := (∅ : Std.HashSet GoalId)
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

unsafe def copyGoals (assignedMVars : UnorderedArraySet MVarId)
    (start : GoalRef) (parentMetaState : Meta.SavedState)
    (parentSuccessProbability : Percent) (depth : Nat) :
    TreeM (Array Goal) := do
  let toCopy ← getGoalsToCopy assignedMVars start
  toCopy.mapM λ gref => do
    let g ← gref.get
    let rs := (← read).ruleSet
    let (forwardState, forwardRuleMatches, mvars) ←
      runInMetaState parentMetaState do
        let start ← start.get
        let diff ← diffGoals start.currentGoal g.preNormGoal
        let (forwardState, ms) ← start.forwardState.applyGoalDiff rs diff
        let forwardRuleMatches :=
          start.forwardRuleMatches.update ms diff.removedFVars
            (consumedForwardRuleMatches := #[]) -- TODO unsure whether this is correct
        let mvars ← .ofHashSet <$> g.preNormGoal.getMVarDependencies
        pure (forwardState, forwardRuleMatches, mvars)
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
      forwardState
      forwardRuleMatches
      successProbability := parentSuccessProbability
      addedInIteration := (← read).currentIteration
      lastExpandedInIteration := Iteration.none
      unsafeRulesSelected := false
      unsafeQueue := {}
      failedRapps := #[]
    }

def makeInitialGoal (goal : Subgoal) (mvars : UnorderedArraySet MVarId)
    (parent : MVarClusterRef) (parentMetaState : Meta.SavedState)
    (parentForwardState : ForwardState)
    (parentForwardMatches : ForwardRuleMatches)
    (consumedForwardRuleMatches : Array ForwardRuleMatch) (depth : Nat)
    (successProbability : Percent) (origin : GoalOrigin) : TreeM Goal := do
  let rs := (← read).ruleSet
  let (forwardState, forwardRuleMatches) ← runInMetaState parentMetaState do
    let (fs, newMatches) ← parentForwardState.applyGoalDiff rs goal.diff
    let ms :=
      parentForwardMatches.update newMatches goal.diff.removedFVars
        consumedForwardRuleMatches
    pure (fs, ms)
  return Goal.mk {
    id := ← getAndIncrementNextGoalId
    children := #[]
    state := GoalState.unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := goal.mvarId
    normalizationState := NormalizationState.notNormal
    forwardState
    forwardRuleMatches
    addedInIteration := (← read).currentIteration
    lastExpandedInIteration := Iteration.none
    unsafeRulesSelected := false
    unsafeQueue := {}
    failedRapps := #[]
    parent, origin, depth, mvars, successProbability
  }

unsafe def addRappUnsafe (r : AddRapp) : TreeM RappRef := do
  let originalSubgoals := r.goals

  let rref : RappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := r.parent
    children := #[] -- will be filled in later
    state := NodeState.unknown
    isIrrelevant := false
    appliedRule := r.appliedRule
    scriptSteps? := r.scriptSteps?
    originalSubgoals := originalSubgoals.map (·.mvarId)
    successProbability := r.successProbability
    metaState := r.postState
    introducedMVars := {} -- will be filled in later
    assignedMVars   := {} -- will be filled in later
  }

  let parentGoal ← r.parent.get
  let goalDepth := parentGoal.depth + 1

  let (originalSubgoalMVars, assignedMVars, assignedOrDroppedMVars) ←
    r.postState.runMetaM' do
      -- Get mvars which the original subgoals depend on.
      let originalSubgoalMVars : Std.HashSet MVarId ←
        originalSubgoals.foldlM (init := ∅) λ acc subgoal =>
          return acc.insertMany (← subgoal.mvarId.getMVarDependencies)

      -- Get mvars which were either assigned or dropped by the rapp. We assume
      -- that rules only assign mvars which appear in the rapp's parent goal. A
      -- dropped mvar is one that appears in the parent of the rapp but is
      -- neither assigned by the rapp nor does it appear in any of its subgoals.
      -- A dropped mvar is treated like an assigned mvar for the purposes of
      -- copying.
      let mut assignedMVars : UnorderedArraySet MVarId := ∅
      let mut assignedOrDroppedMVars : UnorderedArraySet MVarId := ∅
      for mvarId in parentGoal.mvars do
        if ← mvarId.isAssignedOrDelayedAssigned then
          -- mvar was assigned
          assignedMVars := assignedMVars.insert mvarId
          assignedOrDroppedMVars := assignedOrDroppedMVars.insert mvarId
        else if ! originalSubgoalMVars.contains mvarId then
          -- mvar was dropped
          assignedOrDroppedMVars := assignedOrDroppedMVars.insert mvarId
      pure (originalSubgoalMVars, assignedMVars, assignedOrDroppedMVars)

  -- If the rapp assigned or dropped any mvars, copy the related goals.
  let copiedGoals : Array Goal ←
    copyGoals assignedOrDroppedMVars r.parent r.postState
      r.successProbability goalDepth
  let copiedSubgoals : Array Subgoal :=
    copiedGoals.map λ g =>
      { diff := { (default : GoalDiff) with newGoal := g.preNormGoal } }
    -- The diff is irrelevant because we later add `g` to the tree (and the
    -- forward state of `g` is already up to date).

  -- Collect the mvars which occur in the original subgoals and copied goals.
  let originalSubgoalAndCopiedGoalMVars :=
    copiedGoals.foldl (init := originalSubgoalMVars)
       λ copiedGoalMVars g => copiedGoalMVars.insertMany g.mvars

  -- Turn the dropped mvars into subgoals. Note: an mvar that was dropped by the
  -- rapp may occur in the copied goals, in which case we don't count it as
  -- dropped any more.
  let droppedSubgoals : Array Subgoal ← runInMetaState r.postState do
    let mut droppedMVars := #[]
    for mvarId in parentGoal.mvars do
      unless ← (pure $ originalSubgoalAndCopiedGoalMVars.contains mvarId) <||>
               mvarId.isAssignedOrDelayedAssigned do
        let diff ← diffGoals parentGoal.currentGoal mvarId
        droppedMVars := droppedMVars.push { diff }
    pure droppedMVars

  -- Partition the subgoals into 'proper goals' and 'proper mvars'. A proper
  -- mvar is an mvar that occurs in any of the other subgoal mvars. Any other
  -- mvar is a proper goal.
  let (properGoals, _) ← r.postState.runMetaM' do
    partitionGoalsAndMVars (·.mvarId) $
      originalSubgoals ++ copiedSubgoals ++ droppedSubgoals

  -- Construct the subgoals
  let subgoals ← properGoals.mapM λ (goal, mvars) =>
    if let some copiedGoal := copiedGoals.find? (·.preNormGoal == goal.mvarId) then
      pure copiedGoal
    else
      let origin :=
        if droppedSubgoals.find? (·.mvarId == goal.mvarId) |>.isSome then
          .droppedMVar
        else
          .subgoal
      try
        makeInitialGoal goal mvars (unsafeCast ()) r.postState
          parentGoal.forwardState parentGoal.forwardRuleMatches
          r.consumedForwardRuleMatches goalDepth r.successProbability origin
          -- The parent (`unsafeCast ()`) will be patched up later.
      catch e =>
        throwError "in rapp for rule {r.appliedRule.name}:{indentD e.toMessageData}"

  -- Construct the new mvar clusters.
  let crefs : Array MVarClusterRef ←
    cluster (·.mvars.toArray) subgoals |>.mapM λ gs => do
      let grefs ← gs.mapM (IO.mkRef ·)
      let cref ← IO.mkRef $ MVarCluster.mk {
        parent? := some rref
        goals := grefs
        isIrrelevant := false
        state := NodeState.unknown
      }
      -- Patch up information we left out earlier (to break cyclic
      -- dependencies).
      grefs.forM λ gref => gref.modify λ g => g.setParent cref
      return cref

  -- Get the introduced mvars. An mvar counts as introduced by this rapp if it
  -- appears in a subgoal, but not in the parent goal.
  let mut introducedMVars : UnorderedArraySet MVarId := ∅
  let mut allIntroducedMVars ← modifyGetThe Tree λ t =>
    (t.allIntroducedMVars, { t with allIntroducedMVars := ∅ })
    -- We set `allIntroducedMVars := ∅` to make sure that the hash set is used
    -- linearly.
  for g in subgoals do
    for mvarId in g.mvars do
      if ! parentGoal.mvars.contains mvarId &&
         ! allIntroducedMVars.contains mvarId then
        introducedMVars := introducedMVars.insert mvarId
        allIntroducedMVars := allIntroducedMVars.insert mvarId
  modifyThe Tree λ t => { t with allIntroducedMVars }

  -- Patch up more information we left out earlier.
  rref.modify λ r =>
    r.setChildren crefs
    |>.setIntroducedMVars introducedMVars
    |>.setAssignedMVars assignedMVars
  r.parent.modify λ g => g.setChildren $ g.children.push rref

  -- Increment goal and rapp counters.
  incrementNumGoals subgoals.size
  incrementNumRapps
  return rref

/--
Adds a new rapp and its subgoals. If the rapp assigns mvars, all relevant
goals containing these mvars are copied as children of the rapp as well. If
the rapp drops mvars, these are treated as assigned mvars, in the sense that
the same goals are copied as if the dropped mvar had been assigned.

Note that adding a rapp may prove the parent goal, but this function does not
make the necessary changes. So after calling it, you should check whether the
rapp's parent goal is proven and mark it accordingly.
-/
@[implemented_by addRappUnsafe]
opaque addRapp : AddRapp → TreeM RappRef

end Aesop
