/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Tree.State
import Aesop.Tree.Traversal
import Aesop.Tree.TreeM
import Batteries.Lean.HashSet
import Aesop.Tree.RunMetaM

open Lean
open Lean.Meta

namespace Aesop.MVarClusterRef

def checkIds (root : MVarClusterRef) : CoreM Unit := do
  let visitedGoalIds : IO.Ref (Std.HashSet GoalId) ← IO.mkRef {}
  let visitedRappIds : IO.Ref (Std.HashSet RappId) ← IO.mkRef {}
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
    (λ _ => return true)
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

def checkMVars (root : MVarClusterRef) (rootMetaState : Meta.SavedState) :
    MetaM Unit :=
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      checkGoalMVars g
      return true)
    (λ rref => do
      let r ← rref.get
      checkAssignedMVars r
      checkDroppedMVars r
      return true)
    (λ _ => return true)
    (TreeRef.mvarCluster root)
  where
    getParentInfo (r : Rapp) : CoreM (MVarId × Meta.SavedState) := do
      let some res := (← r.parent.get).postNormGoalAndMetaState? | throwError
        "{Check.tree.name}: expected parent goal of rapp {r.id} to be normalised (but not proven by normalisation)."
      return res

    checkAssignedMVars (r : Rapp) : MetaM Unit := do
      let (parentPostNormGoal, parentPostNormState) ← getParentInfo r
      let actualAssigned :=
        (← getAssignedExprMVars parentPostNormState r.metaState).erase
          parentPostNormGoal
      unless actualAssigned.equalSet r.assignedMVars.toArray do throwError
        "{Check.tree.name}: rapp {r.id} reports incorrect assigned mvars.\n  reported: {r.assignedMVars.toArray.map (·.name)}\n  actual: {actualAssigned.map (·.name)}"

    checkDroppedMVars (r : Rapp) : MetaM Unit := do
      let droppableMVars :=
        (← r.parent.get).mvars ++ r.introducedMVars |>.toArray
      let mut nonDroppedMVars := Std.HashSet.ofArray r.assignedMVars.toArray
      for cref in r.children do
        for gref in (← cref.get).goals do
          let g ← gref.get
          nonDroppedMVars := nonDroppedMVars.insert g.preNormGoal
          nonDroppedMVars := nonDroppedMVars.insertMany g.mvars
      if droppableMVars.any (! nonDroppedMVars.contains ·) then throwError
        "{Check.tree.name}: rapp {r.id} dropped mvars.\n  mvars introduced or present in parent: {droppableMVars.map (·.name)}\n  mvars assigned or present in subgoals:\n  {nonDroppedMVars.toArray.map (·.name)}"

    checkGoalMVars (g : Goal) : MetaM Unit := do
      checkNormMVars g
      let actualPreNormMVars ← g.runMetaMInParentState'
        g.preNormGoal.getMVarDependencies
      let expectedMVars := Std.HashSet.ofArray g.mvars.toArray
      unless actualPreNormMVars == expectedMVars do throwError
        "{Check.tree.name}: goal {g.id} reports incorrect unassigned mvars.\n  reported: {g.mvars.toArray.map (·.name)}\n  actual: {actualPreNormMVars.toArray.map (·.name)}"

    checkNormMVars (g : Goal) : MetaM Unit := do
      let go (parentMetaState postMetaState : Meta.SavedState)
          (introduced : Array MVarId) : MetaM Unit := do
        unless introduced.isEmpty do throwError
          "{Check.tree.name}: normalisation of goal {g.id} introduced additional metavariables:{indentD $ toMessageData $ introduced.map (·.name)}"
        let assigned :=
          (← getAssignedExprMVars parentMetaState postMetaState).erase
            g.preNormGoal
        unless assigned.isEmpty do throwError
          "{Check.tree.name}: normalisation of goal {g.id} assigned metavariables:{indentD $ toMessageData $ assigned.map (·.name)}"
      match g.normalizationState with
      | .notNormal => return
      | .provenByNormalization postMetaState .. =>
        let parentMetaState ← g.parentMetaState rootMetaState
        let introduced ← getIntroducedExprMVars parentMetaState postMetaState
        go parentMetaState postMetaState introduced
      | .normal postGoal postMetaState .. =>
        let parentMetaState ← g.parentMetaState rootMetaState
        let introduced :=
          (← getIntroducedExprMVars parentMetaState postMetaState).erase
            postGoal
        go parentMetaState postMetaState introduced

-- Check that each mvar ocurring in a goal is either present in the root meta
-- state or has an introducing rapp.
def checkIntroducedMVars (root : MVarClusterRef)
    (rootMetaState : Meta.SavedState) : MetaM Unit := do
  let declaredAtRoot : Std.HashSet MVarId :=
    rootMetaState.meta.mctx.decls.foldl (init := ∅) λ acc mvarId _ =>
      acc.insert mvarId
  let introducedMVarsRef ← IO.mkRef declaredAtRoot
  preTraverseDown
    (λ gref => do
      for mvarId in (← gref.get).mvars do
        unless (← introducedMVarsRef.get).contains mvarId do
          throwError "{Check.tree.name}: at goal {(← gref.get).id}: no introducing rapp found for mvarId {mvarId.name}"
      return true)
    (λ rref => do
      let introduced := (← rref.get).introducedMVars
      introducedMVarsRef.modify λ mvars => mvars.insertMany introduced
      return true)
    (λ _ => return true)
    (.mvarCluster root)

def checkInvariants (root : MVarClusterRef) (rootMetaState : Meta.SavedState) :
    MetaM Unit := do
  root.checkAcyclic
  root.checkConsistentParentChildLinks
  root.checkIds
  root.checkState
  root.checkIrrelevance
  root.checkMVars rootMetaState
  root.checkIntroducedMVars rootMetaState

def checkInvariantsIfEnabled (root : MVarClusterRef)
    (rootMetaState : Meta.SavedState) : MetaM Unit := do
  if ← Check.tree.isEnabled then
    root.checkInvariants rootMetaState

end MVarClusterRef

def checkInvariantsIfEnabled : TreeM Unit := do
  (← getRootMVarCluster).checkInvariantsIfEnabled (← getRootMetaState)

end Aesop
