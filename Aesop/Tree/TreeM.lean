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

def mkInitialTree (goal : MVarId) (rs : LocalRuleSet) : MetaM Tree := do
  let rootClusterRef ← IO.mkRef $ MVarCluster.mk {
    parent? := none
    goals := #[] -- patched up below
    isIrrelevant := false
    state := NodeState.unknown
  }
  let (forwardState, ms) ← withConstAesopTraceNode .forward (return m!"building initial forward state") do
    -- NOTE we don't cache rule pattern lookups here. It would be possible to do
    -- so, but doesn't seem worth the trouble.
    have : MonadRulePatternCache MetaM := {
      findCached? := λ _ => return none
      cache := λ _ _ => return
    }
    -- Ditto for the RPINF cache
    have : MonadRPINF MetaM := {
      get := return default
      set := λ _ => return default
      modifyGet := λ f => return f default |>.fst
    }
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
  rulePatternCache : RulePatternCache
  rpinfCache : RPINFCache

abbrev TreeM := ReaderT TreeM.Context $ StateRefT TreeM.State MetaM

namespace TreeM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad TreeM :=
  { inferInstanceAs (Monad TreeM) with }

instance (priority := low) : MonadStateOf Tree TreeM where
  get := return (← get).tree
  set tree := modify ({ · with tree })
  modifyGet f := modifyGet λ s =>
    let (a, tree) := f s.tree
    (a, { s with tree })

instance : Inhabited (TreeM α) where
  default := failure

def run' (ctx : TreeM.Context) (tree : Tree) (x : TreeM α) :
    MetaM (α × TreeM.State) :=
  ReaderT.run x ctx |>.run { tree, rulePatternCache := ∅, rpinfCache := ∅ }

end TreeM

def getRootMVarCluster : TreeM MVarClusterRef :=
  return (← get).tree.root

def getRootMetaState : TreeM Meta.SavedState :=
  return (← get).tree.rootMetaState

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
  modify λ s => { s with tree.numGoals := s.tree.numGoals + increment }

def incrementNumRapps (increment := 1) : TreeM Unit := do
  modify λ s => { s with tree.numRapps := s.tree.numRapps + increment }

def getAllIntroducedMVars : TreeM (Std.HashSet MVarId) :=
  return (← get).tree.allIntroducedMVars

def getAndIncrementNextGoalId : TreeM GoalId := do
  modifyGet λ t =>
    let curr := t.tree.nextGoalId
    (curr, { t with tree.nextGoalId := curr.succ })

def getAndIncrementNextRappId : TreeM RappId := do
  modifyGet λ t =>
    let curr := t.tree.nextRappId
    (curr, { t with tree.nextRappId := curr.succ })

def getResetRulePatternCache : TreeM RulePatternCache :=
  modifyGet λ s => (s.rulePatternCache, { s with rulePatternCache := ∅ })

def setRulePatternCache (cache : RulePatternCache): TreeM Unit :=
  modify λ s => { s with rulePatternCache := cache }

def getResetRPINFCache : TreeM RPINFCache :=
  modifyGet λ s => (s.rpinfCache, { s with rpinfCache := ∅ })

def setRPINFCache (cache : RPINFCache): TreeM Unit :=
  modify λ s => { s with rpinfCache := cache }

end Aesop
