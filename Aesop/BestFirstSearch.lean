/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Rule
import Aesop.Tree
import Aesop.Util

open Lean
open Lean.Meta
open Std (BinomialHeap)

namespace Aesop.Search

structure ActiveGoal where
  goal : GoalRef
  successProbability : Percent

namespace ActiveGoal

instance : LT ActiveGoal where
  lt g h := g.successProbability < h.successProbability

instance : DecidableRel (α := ActiveGoal) (· < ·) :=
  λ g h =>
    inferInstanceAs (Decidable (g.successProbability < h.successProbability))

end ActiveGoal

abbrev ActiveGoalQueue := BinomialHeap ActiveGoal (· > ·)
  -- ActiveGoals are ordered by success probability. Here we want highest
  -- success probability first.

structure State where
  tree : Tree
  activeGoals : ActiveGoalQueue

namespace State

def mkInitial (t : Tree) : State where
  tree := t
  activeGoals := BinomialHeap.empty

def mkInitialForMainGoal (mainGoal : MVarId) : MetaM State := do
  let goal ← copyMVar mainGoal
  let tree ← Tree.singleton $
    Goal.mk none #[] $ GoalData.mkInitial goal Percent.hundred
  return State.mkInitial tree

end State

abbrev SearchM := StateRefT State MetaM

namespace SearchM

def run (mainGoal : MVarId) (x : SearchM α) : MetaM (α × State) := do
  let s ← State.mkInitialForMainGoal mainGoal
  StateRefT'.run x s

instance : MonadStateOf Tree SearchM :=
  MonadStateOf.ofLens State.tree (λ t s => { s with tree := t })

instance : MonadStateOf ActiveGoalQueue SearchM :=
  MonadStateOf.ofLens State.activeGoals (λ an s => { s with activeGoals := an })

end SearchM

def addGoal (goal : MVarId) (successProbability : Percent)
    (parent : RappRef) : SearchM GoalRef := do
  let g ← GoalData.mkInitial goal successProbability
  let t ← getThe Tree
  let (_, gref, t) ← t.insertGoal g parent
  setThe Tree t
  modifyThe ActiveGoalQueue λ q => q.insert
    { goal := gref
      successProbability := successProbability }
  return gref

-- TODO array?
def addGoals (goals : List MVarId) (successProbability : Percent)
    (parent : RappRef) : SearchM (List GoalRef) := do
  let mut acc := []
  for goal in goals do
    let gref ← addGoal goal successProbability parent
    acc := gref :: acc
  return acc.reverse

def runRule (goal : MVarId) (r : MVarId → MetaM (List MVarId)) :
    MetaM (Option (MVarId × List MVarId)) := do
  let proofMVar ← copyMVar goal
  let subgoals ← observing? $ r proofMVar
  return subgoals.map (proofMVar, ·)

inductive RuleResult
| proven
| failed
| succeeded

def applyRegularRule (parentRef : GoalRef) (rule : RegularRule) :
    SearchM RuleResult := do
  let state ← getThe State
  let parent ← parentRef.get
  let result ← runRule parent.goal rule.tac
  let successProbability :=
    parent.successProbability * rule.successProbability
  match result with
  | some (proofMVar, []) => do
    -- Rule succeeded and did not generate subgoals, meaning the parent
    -- node is proven.
    let r :=
      { RappData.mkInitial rule successProbability (mkMVar proofMVar) with
        proven? := true }
    let (_, _, tree) ← state.tree.insertRapp r parentRef
    setThe Tree tree
    parentRef.setProven
    return RuleResult.proven
  | some (proofMVar, subgoals) => do
    -- Rule succeeded and generated subgoals.
    let r := RappData.mkInitial rule successProbability (mkMVar proofMVar)
    let (_, rappRef, tree) ← state.tree.insertRapp r parentRef
    setThe Tree tree
    let _ ← addGoals subgoals successProbability rappRef
    return RuleResult.succeeded
  | none => do
    -- Rule did not succeed.
    parentRef.modify λ (g : Goal) => g.setFailedRapps $ rule :: g.failedRapps
    parentRef.setUnprovable
    return RuleResult.failed

def runNormalizationRule (goal : MVarId) (r : NormalizationRule) :
    SearchM MVarId := do
  let subgoals ← try r.tac goal catch e => throwError
    "aesop: normalization rule {r.name} failed with error:\n{e.toMessageData}"
    -- TODO show error context
  match subgoals with
  | [g] => return g
  | _ => throwError "aesop: normalization rule {r.name} did not produce exactly one subgoal"

def runNormalizationSimp (goal : MVarId) (ctx : Simp.Context) : SearchM MVarId := do
  let (some goal) ← simpAll goal ctx | throwError
    "aesop: normalization simp rule solved the goal"
  return goal

def normalizeGoalMVar (rs : RuleSet) (goal : MVarId) : SearchM MVarId := do
  let rules ← rs.applicableNormalizationRules goal
  let (preSimpRules, postSimpRules) :=
    rules.partition λ r => r.priorityInfo < (0 : Int)
  let goal ← preSimpRules.foldlM (init := goal) runNormalizationRule
  let simpCtx :=
    { (← Simp.Context.mkDefault) with simpLemmas := rs.normalizationSimpLemmas }
  let goal ← runNormalizationSimp goal simpCtx
  let goal ← postSimpRules.foldlM (init := goal) runNormalizationRule
  return goal

def normalizeGoalIfNecessary (rs : RuleSet) (gref : GoalRef) : SearchM Unit :=
  gref.modifyM λ g => do
    let (false) ← pure g.normal? | return g
    let newGoal ← normalizeGoalMVar rs g.goal
    return g.setGoal newGoal

end Aesop.Search

namespace Aesop

export Aesop.Search (SearchM)

end Aesop
