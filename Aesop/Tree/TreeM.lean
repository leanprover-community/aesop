/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State.Initial
import Aesop.RuleSet
import Aesop.Tree.Data

open Lean
open Lean.Meta

namespace Aesop

structure Tree where
  root : MVarClusterRef
  rootMetaState : Meta.SavedState
  numGoals : Nat
  numRapps : Nat
  nextGoalId : GoalId
  nextRappId : RappId
  /--
  Union of the mvars introduced by all rapps.
  -/
  allIntroducedMVars : Std.HashSet MVarId

def mkInitialTree (goal : MVarId) (rs : LocalRuleSet) : BaseM Tree := do
  let rootClusterRef ← IO.mkRef $ MVarCluster.mk {
    parent? := none
    goals := #[] -- patched up below
    isIrrelevant := false
    state := NodeState.unknown
  }
  let (forwardState, ms) ← withConstAesopTraceNode .forward (return m!"building initial forward state") do
    rs.mkInitialForwardState goal
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
    mvars := .ofHashSet (← goal.getMVarDependencies)
    forwardState
    forwardRuleMatches := .ofArray ms
    successProbability := Percent.hundred
    addedInIteration := Iteration.one
    lastExpandedInIteration := Iteration.none
    unsafeRulesSelected := false
    unsafeQueue := {}
    failedRapps := #[]
  }
  rootClusterRef.modify λ c => c.setGoals #[rootGoalRef]
  return {
    root := rootClusterRef
    rootMetaState := ← saveState
    numGoals := 1
    numRapps := 0
    nextGoalId := .one
    nextRappId := .zero
    allIntroducedMVars := ∅
  }

structure TreeM.Context where
  currentIteration : Iteration
  ruleSet : LocalRuleSet

structure TreeM.State where
  tree : Tree

abbrev TreeM := ReaderT TreeM.Context $ StateRefT TreeM.State BaseM

namespace TreeM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad TreeM :=
  { inferInstanceAs (Monad TreeM) with }

instance (priority := low) : MonadStateOf Tree TreeM where
  get := return (← getThe State).tree
  set tree := modifyThe State ({ · with tree })
  modifyGet f := modifyGetThe State λ s =>
    let (a, tree) := f s.tree
    (a, { s with tree })

instance : Inhabited (TreeM α) where
  default := failure

def run' (ctx : TreeM.Context) (tree : Tree) (x : TreeM α) :
    BaseM (α × TreeM.State) :=
  ReaderT.run x ctx |>.run { tree }

end TreeM

def getRootMVarCluster : TreeM MVarClusterRef :=
  return (← getThe Tree).root

def getRootMetaState : TreeM Meta.SavedState :=
  return (← getThe Tree).rootMetaState

def getRootGoal : TreeM GoalRef := do
  let cref ← getRootMVarCluster
  let grefs := (← cref.get).goals
  if h : grefs.size = 1 then
    return grefs[0]
  else
    throwError "aesop: internal error: unexpected number of goals in root mvar cluster: {grefs.size}"

def getRootMVarId : TreeM MVarId := do
  let gref ← getRootGoal
  return (← gref.get).preNormGoal

def incrementNumGoals (increment := 1) : TreeM Unit := do
  modifyThe Tree λ s => { s with numGoals := s.numGoals + increment }

def incrementNumRapps (increment := 1) : TreeM Unit := do
  modifyThe Tree λ s => { s with numRapps := s.numRapps + increment }

def getAllIntroducedMVars : TreeM (Std.HashSet MVarId) :=
  return (← getThe Tree).allIntroducedMVars

def getAndIncrementNextGoalId : TreeM GoalId := do
  modifyGetThe Tree λ t =>
    let curr := t.nextGoalId
    (curr, { t with nextGoalId := curr.succ })

def getAndIncrementNextRappId : TreeM RappId := do
  modifyGetThe Tree λ t =>
    let curr := t.nextRappId
    (curr, { t with nextRappId := curr.succ })

end Aesop
