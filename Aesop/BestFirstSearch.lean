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

def ofGoalRef [Monad m] [MonadLiftT (ST IO.RealWorld) m] (gref : GoalRef) :
    m ActiveGoal :=
  return {
    goal := gref
    successProbability := (← gref.get).successProbability
  }

end ActiveGoal

abbrev ActiveGoalQueue := BinomialHeap ActiveGoal (· > ·)
  -- ActiveGoals are ordered by success probability. Here we want highest
  -- success probability first.

structure Context where
  ruleSet : RuleSet
  mainGoal : MVarId

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

abbrev SearchM := ReaderT Context $ StateRefT State MetaM

namespace SearchM

def run (ctx : Context) (state : State) (x : SearchM α) : MetaM (α × State) :=
  StateRefT'.run (ReaderT.run x ctx) state

end SearchM

instance (priority := 0) : MonadReaderOf RuleSet SearchM where
  read := Context.ruleSet <$> read

instance (priority := 0) : MonadStateOf Tree SearchM :=
  MonadStateOf.ofLens State.tree (λ t s => { s with tree := t })

instance (priority := 0) : MonadStateOf ActiveGoalQueue SearchM :=
  MonadStateOf.ofLens State.activeGoals (λ an s => { s with activeGoals := an })

def readMainGoal : SearchM MVarId :=
  Context.mainGoal <$> read

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
    (parent : RappRef) : SearchM (Array GoalRef) := do
  let mut acc := #[]
  for goal in goals do
    let gref ← addGoal goal successProbability parent
    acc := acc.push gref
  return acc

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

def normalizeGoalMVar (goal : MVarId) : SearchM MVarId := do
  let rs ← readThe RuleSet
  let rules ← rs.applicableNormalizationRules goal
  let (preSimpRules, postSimpRules) :=
    rules.partition λ r => r.priorityInfo < (0 : Int)
  let goal ← preSimpRules.foldlM (init := goal) runNormalizationRule
  let simpCtx :=
    { (← Simp.Context.mkDefault) with simpLemmas := rs.normalizationSimpLemmas }
  let goal ← runNormalizationSimp goal simpCtx
  let goal ← postSimpRules.foldlM (init := goal) runNormalizationRule
  return goal

def normalizeGoalIfNecessary (gref : GoalRef) : SearchM Unit :=
  gref.modifyM λ g => do
    let (false) ← pure g.normal? | return g
    let newGoal ← normalizeGoalMVar g.goal
    return g.setGoal newGoal

def runRule (goal : MVarId) (r : MVarId → MetaM (List MVarId)) :
    MetaM (Option (MVarId × List MVarId)) := do
  let proofMVar ← copyMVar goal
  let subgoals ← observing? $ r proofMVar
  return subgoals.map (proofMVar, ·)

inductive RuleResult
| proven
| failed
| succeeded

namespace RuleResult

def failed? : RuleResult → Bool
  | failed => true
  | _ => false

end RuleResult

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

def applyFirstSafeRule (gref : GoalRef) : SearchM RuleResult := do
  let g ← gref.get
  let rules ← (← readThe RuleSet).applicableSafeRules g.goal
  let mut result := RuleResult.failed
  for r in rules do
    result ← applyRegularRule gref $ RegularRule.safe r
    if result.failed? then continue else break
  return result

def selectRules (gref : GoalRef) : SearchM (List UnsafeRule) := do
  let g ← gref.get
  match g.unsafeQueue with
  | some rules => return rules
  | none => do
    let rs ← readThe RuleSet
    let rules := (← rs.applicableUnsafeRules g.goal).toList
    gref.set $ g.setUnsafeQueue rules
    return rules

def applyFirstUnsafeRule (gref : GoalRef) : SearchM Bool := do
  let rules ← selectRules gref
  let mut result := RuleResult.failed
  let mut remainingRules := rules
  for r in rules do
    remainingRules := remainingRules.tail!
    result ← applyRegularRule gref (RegularRule.unsafe r)
    if result.failed? then continue else break
  gref.modify λ g => g.setUnsafeQueue remainingRules
  if result.failed? && remainingRules.isEmpty then gref.setUnprovable
  return ¬ remainingRules.isEmpty

def expandGoal (gref : GoalRef) : SearchM Bool := do
  normalizeGoalIfNecessary gref
  let result ← applyFirstSafeRule gref
  if result.failed?
    then applyFirstUnsafeRule gref
    else pure false

def expandNextGoal : SearchM Unit := do
  let some (activeGoal, activeGoals) ← pure (← getThe ActiveGoalQueue).removeMin
    | throwError "aesop/expandNextGoal: internal error: no active goals left"
  setThe ActiveGoalQueue activeGoals
  let gref := activeGoal.goal
  let g ← gref.get
  unless g.proven? ∨ g.unprovable? ∨ g.irrelevant? do
    let hasMoreRules ← expandGoal gref
    if hasMoreRules then do
      let ag ← ActiveGoal.ofGoalRef gref
      modifyThe ActiveGoalQueue λ q => q.insert ag

def finishIfProven : SearchM Bool := do
  let t ← getThe Tree
  let (true) ← pure (← t.root.get).proven?
    | return false
  t.linkProofs
  let prf ← t.extractProof
  assignExprMVar (← readMainGoal) prf
  return true

partial def search : SearchM Unit := do
  let t ← getThe Tree
  let (false) ← t.rootUnprovable?
    | throwError "aesop: failed to prove the goal"
  let done ← finishIfProven
  if ¬ done then
    expandNextGoal
    search

end Search

def search (rs : RuleSet) (mainGoal : MVarId) : MetaM Unit := do
  let state ← Search.State.mkInitialForMainGoal mainGoal
  let ctx := { ruleSet := rs, mainGoal := mainGoal }
  let _ ← Search.search.run ctx state

end Aesop
