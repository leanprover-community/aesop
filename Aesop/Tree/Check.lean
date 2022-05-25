/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Tree.State
import Aesop.Tree.Traversal
import Aesop.Tree.TreeM

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop.MVarClusterRef

def checkIds (root : MVarClusterRef) : CoreM Unit := do
  let visitedGoalIds : IO.Ref (HashSet GoalId) ← IO.mkRef {}
  let visitedRappIds : IO.Ref (HashSet RappId) ← IO.mkRef {}
  preTraverseDown
    (λ gref => do
      let id := (← gref.get).id
      if (← visitedGoalIds.get).contains id then
        throwError "{Check.tree.name}: duplicate goal id: {id}"
      visitedGoalIds.modify λ s => s.insert id
      return true)
    (λ rref => do
      let id := (← rref.get).id
      if (← visitedRappIds.get).contains id then
        throwError "{Check.tree.name}: duplicate rapp id: {id}"
      visitedRappIds.modify λ s => s.insert id
      return true)
    (λ cref => return true)
    (TreeRef.mvarCluster root)

def checkAcyclic (root : MVarClusterRef) : CoreM Unit := do
  -- We use arrays to store the visited nodes (rather than some data structure
  -- with asymptotically faster lookup) because STRefs only have pointer
  -- equality, not pointer comparison. Besides, this is probably faster anyway
  -- for small to medium trees.
  let visitedGoalRefs        : IO.Ref (Array GoalRef)        ← ST.mkRef #[]
  let visitedRappRefs        : IO.Ref (Array RappRef)        ← ST.mkRef #[]
  let visitedMVarClusterRefs : IO.Ref (Array MVarClusterRef) ← ST.mkRef #[]
  preTraverseDown
    (λ gref => go visitedGoalRefs gref)
    (λ rref => go visitedRappRefs rref)
    (λ cref => go visitedMVarClusterRefs cref)
    (TreeRef.mvarCluster root)
  where
    go {α} (visited : IO.Ref (Array (IO.Ref α))) (current : IO.Ref α) :
        CoreM Bool := do
      if ← (← visited.get).anyM (current.ptrEq ·) then throwError
        "{Check.tree.name}: search tree contains a cycle."
      visited.modify (·.push current)
      return true

def checkConsistentParentChildLinks (root : MVarClusterRef) : CoreM Unit :=
  preTraverseDown
    (λ gref => do
      for c in (← gref.get).children do
        if ← notM $ (← c.get).parent.ptrEq gref then err
      return true)
    (λ rref => do
      for c in (← rref.get).children do
        match (← c.get).parent? with
        | some parent =>
          if ← notM $ parent.ptrEq rref then err
        | none =>
          err
      return true)
    (λ cref => do
      for c in (← cref.get).goals do
        if ← notM $ (← c.get).parent.ptrEq cref then err
      return true)
    (TreeRef.mvarCluster root)
  where
    err := throwError "{Check.tree.name}: search tree is not properly linked."

private def mvarClusterId (c : MVarCluster) : BaseIO String :=
  match c.parent? with
  | some parentRef => return s!"mvar cluster of rapp {(← parentRef.get).id}"
  | none => return s!"root mvar cluster"

def checkState (root : MVarClusterRef) : CoreM Unit :=
  postTraverseDown
    (λ gref => do
      let g ← gref.get
      go s!"goal {g.id}" (← g.stateNoCache) g.state)
    (λ rref => do
      let r ← rref.get
      go s!"rapp {r.id}" (← r.stateNoCache) r.state)
    (λ cref => do
      let c ← cref.get
      go (← mvarClusterId c) (← c.stateNoCache) c.state)
    (TreeRef.mvarCluster root)
  where
    @[inline]
    go {σ} [BEq σ] [ToString σ] (id : String) (expected actual : σ) :
        CoreM Unit := do
      if expected != actual then throwError
        "{Check.tree.name}: {id} has wrong state: marked as '{actual}' but should be '{expected}'."

def checkIrrelevance (root : MVarClusterRef) : CoreM Unit :=
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      go s!"goal {g.id}" (← g.isIrrelevantNoCache) g.isIrrelevant)
    (λ rref => do
      let r ← rref.get
      go s!"rapp {r.id}" (← r.isIrrelevantNoCache) r.isIrrelevant)
    (λ cref => do
      let c ← cref.get
      go (← mvarClusterId c) (← c.isIrrelevantNoCache) c.isIrrelevant)
    (TreeRef.mvarCluster root)
  where
    @[inline]
    go (id : String) (expected actual : Bool) : CoreM Bool := do
      match actual, expected with
      | true, false => throwError
        "{Check.tree.name}: {id} is marked as irrelevant, but is not irrelevant."
      | false, true => throwError
        "{Check.tree.name}: {id} is marked as not irrelevant, but is irrelevant."
      | _, _ => return true

def checkMVars (root : MVarClusterRef) : MetaM Unit := do
  preTraverseDown
    (λ gref => do
      checkGoalMVars (← gref.get)
      return true)
    (λ rref => do
      let r ← rref.get
      checkIntroducedMVars r
      checkAssignedMVars r
      return true)
    (λ cref => return true)
    (TreeRef.mvarCluster root)

  where
    getParentInfo (r : Rapp) : CoreM (MVarId × Meta.SavedState) := do
      let some res := (← r.parent.get).postNormGoalAndMetaState? | throwError
        "{Check.tree.name}: expected parent goal of rapp {r.id} to be normalised (but not proven by normalisation)."
      return res

    checkIntroducedMVars (r : Rapp) : MetaM Unit := do
      let (parentPostNormGoal, parentPostNormState) ← getParentInfo r
      let subgoalMVars ← r.foldSubgoalsM (init := #[]) λ mvars gref =>
        return mvars.push (← gref.get).preNormGoal
      let actualIntroduced :=
        (← introducedExprMVars parentPostNormState r.metaState).filter
          (! subgoalMVars.contains ·)
      if ! actualIntroduced.equalSet r.introducedMVars then throwError
        "{Check.tree.name}: rapp {r.id} reports incorrect introduced mvars.\n  reported: {r.introducedMVars.map (·.name)}\n  actual: {actualIntroduced.map (·.name)}"

    checkAssignedMVars (r : Rapp) : MetaM Unit := do
      let (parentPostNormGoal, parentPostNormState) ← getParentInfo r
      let actualAssigned :=
        (← assignedExprMVars parentPostNormState r.metaState).erase
          parentPostNormGoal
      if ! actualAssigned.equalSet r.assignedMVars then throwError
        "{Check.tree.name}: rapp {r.id} reports incorrect assigned mvars.\n  reported: {r.assignedMVars.map (·.name)}\n  actual: {actualAssigned.map (·.name)}"

    checkGoalMVars (g : Goal) : MetaM Unit := do
      let actualPreNormMVars ←
        g.runMetaMInParentState' $ getGoalMVarsNoDelayed g.preNormGoal
      if let (some (postNormGoal, postNormState)) := g.postNormGoalAndMetaState? then
        let actualPostNormMVars ←
          postNormState.runMetaM' $ getGoalMVarsNoDelayed postNormGoal
        if ! actualPreNormMVars == actualPostNormMVars then throwError
          "{Check.tree.name}: goal {g.id} contains different unassigned mvars pre- and post-normalisation.\n  pre  normalisation: {actualPreNormMVars.toArray.map (·.name)}\n  post normalisation: {actualPostNormMVars.toArray.map (·.name)}"
      let expectedMVars := HashSet.ofArray g.mvars
      if ! actualPreNormMVars == expectedMVars then throwError
        "{Check.tree.name}: goal {g.id} reports incorrect unassigned mvars.\n  reported: {g.mvars.map (·.name)}\n  actual: {actualPreNormMVars.toArray.map (·.name)}"

    checkNormMVars (g : Goal) : MetaM Unit := do
      let go (parentMetaState postMetaState : Meta.SavedState)
          (introduced : Array MVarId) : MetaM Unit := do
        unless introduced.isEmpty do throwError
          "{Check.tree.name}: normalisation of goal {g.id} introduced additional metavariables:{indentD $ toMessageData $ introduced.map (·.name)}"
        let assigned :=
          (← assignedExprMVars parentMetaState postMetaState).erase g.preNormGoal
        unless assigned.isEmpty do throwError
          "{Check.tree.name}: normalisation of goal {g.id} assigned metavariables:{indentD $ toMessageData $ assigned.map (·.name)}"
      match g.normalizationState with
      | NormalizationState.notNormal => return
      | NormalizationState.provenByNormalization postMetaState =>
        let parentMetaState ← g.parentMetaState
        let introduced ← introducedExprMVars parentMetaState postMetaState
        go parentMetaState postMetaState introduced
      | NormalizationState.normal postGoal postMetaState =>
        let parentMetaState ← g.parentMetaState
        let introduced :=
          (← introducedExprMVars parentMetaState postMetaState).erase postGoal
        go parentMetaState postMetaState introduced

def checkInvariants (root : MVarClusterRef) : MetaM Unit := do
  root.checkAcyclic
  root.checkConsistentParentChildLinks
  root.checkIds
  root.checkState
  root.checkIrrelevance
  root.checkMVars

def checkInvariantsIfEnabled (root : MVarClusterRef) : MetaM Unit := do
  if ← Check.tree.isEnabled then
    root.checkInvariants

end MVarClusterRef

def checkInvariantsIfEnabled : TreeM Unit := do
  (← get).root.checkInvariantsIfEnabled

end Aesop
