/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tree.RunMetaM

open Lean
open Lean.Meta

namespace Aesop

structure Tree where
  root : MVarClusterRef
  numGoals : Nat
  numRapps : Nat
  nextGoalId : GoalId
  nextRappId : RappId

def mkInitialTree (goal : MVarId) : MetaM Tree := do
  let mvars ← getUnassignedGoalMVarDependencies goal
  unless mvars.isEmpty do
    throwError "aesop: the goal contains metavariables, which is not currently supported."
    -- TODO support this
  let rootClusterRef ← IO.mkRef $ MVarCluster.mk {
    parent? := none
    goals := #[] -- patched up below
    isIrrelevant := false
    state := NodeState.unknown
  }
  let rootGoalRef ← IO.mkRef $ Goal.mk {
    id := GoalId.zero
    parent := rootClusterRef
    children := #[]
    origin := .subgoal
    depth := 0
    state := GoalState.unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := goal
    normalizationState := NormalizationState.notNormal
    mvars := {} -- TODO update when we allow metas in the inital goal
    successProbability := Percent.hundred
    addedInIteration := Iteration.one
    lastExpandedInIteration := Iteration.none
    unsafeRulesSelected := false
    unsafeQueue := {}
    branchState := {}
    failedRapps := #[]
  }
  rootClusterRef.modify λ c => c.setGoals #[rootGoalRef]
  return {
    root := rootClusterRef
    numGoals := 1
    numRapps := 0
    nextGoalId := GoalId.one
    nextRappId := RappId.zero
  }

structure TreeM.Context where
  currentIteration : Iteration

abbrev TreeM := ReaderT TreeM.Context $ StateRefT Tree MetaM

namespace TreeM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad TreeM :=
  { inferInstanceAs (Monad TreeM) with }

instance (priority := low) : Inhabited (TreeM α) where
  default := failure

def run' (ctx : TreeM.Context) (t : Tree) (x : TreeM α) :
    MetaM (α × Tree) :=
  ReaderT.run x ctx |>.run t

end TreeM


def getRootMVarCluster : TreeM MVarClusterRef :=
  return (← get).root

def getRootGoal : TreeM GoalRef := do
  let cref ← getRootMVarCluster
  let grefs := (← cref.get).goals
  if h : grefs.size = 1 then
    return grefs.get ⟨0, by simp [h]⟩
  else
    throwError "aesop: internal error: unexpected number of goals in root mvar cluster: {grefs.size}"

def incrementNumGoals (increment := 1) : TreeM Unit := do
  modify λ s => { s with numGoals := s.numGoals + increment }

def incrementNumRapps (increment := 1) : TreeM Unit := do
  modify λ s => { s with numRapps := s.numRapps + increment }

def getAndIncrementNextGoalId : TreeM GoalId := do
  let t ← get
  let curr := t.nextGoalId
  set { t with nextGoalId := curr.succ }
  return curr

def getAndIncrementNextRappId : TreeM RappId := do
  let t ← get
  let curr := t.nextRappId
  set { t with nextRappId := curr.succ }
  return curr

end Aesop
