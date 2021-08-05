/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

-- TODO If a 'finished' proof contains metavariables, what should we do?
-- TODO disable safe rules in the presence of unification goals

import Aesop.Check
import Aesop.Options
import Aesop.Rule
import Aesop.Tree
import Aesop.Util

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Std

namespace Aesop

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
  options : Aesop.Options
  mainGoal : MVarId
  rootGoal : GoalRef

structure State where
  activeGoals : ActiveGoalQueue
  nextGoalId : GoalId
  nextRappId : RappId
  numGoals : Nat
    -- As currently implemented, numGoals is exactly nextGoalId (and similar
    -- for rapps). But these are conceptually different things, so we should
    -- track them separately.
  numRapps : Nat

def mkInitialContextAndState (rs : RuleSet) (options : Aesop.Options)
    (mainGoal : MVarId) : MetaM (Context × State) := do
  let rootGoal := Goal.mk none #[] $
    GoalData.mkInitial GoalId.zero mainGoal Percent.hundred
  let rootGoalRef ← ST.mkRef rootGoal
  let ctx := {
    ruleSet := rs
    options := options
    mainGoal := mainGoal
    rootGoal := rootGoalRef }
  let state := {
    activeGoals := BinomialHeap.empty.insert
      { goal := rootGoalRef, successProbability := Percent.hundred }
    nextGoalId := GoalId.one
    nextRappId := RappId.zero
    numGoals := 1
    numRapps := 0 }
  return (ctx, state)

abbrev SearchM := ReaderT Context $ StateRefT State MetaM

namespace SearchM

-- Make the compiler generate specialized `pure`/`bind` so we do not have to
-- optimize through the whole monad stack at every use site.
instance : Monad SearchM := { inferInstanceAs (Monad SearchM) with }

instance (priority := low) : MonadReaderOf RuleSet SearchM where
  read := return (← read).ruleSet

instance (priority := low) : MonadWithReaderOf RuleSet SearchM where
  withReader f := withReader (λ ctx => { ctx with ruleSet := f ctx.ruleSet })

instance (priority := low) : MonadReaderOf Aesop.Options SearchM where
  read := return (← read).options

instance (priority := low) : MonadWithReaderOf Aesop.Options SearchM where
  withReader f := withReader (λ ctx => { ctx with options := f ctx.options })

instance (priority := low) : MonadStateOf GoalId SearchM :=
  MonadStateOf.ofLens State.nextGoalId (λ id s => { s with nextGoalId := id })

instance (priority := low) : MonadStateOf RappId SearchM :=
  MonadStateOf.ofLens State.nextRappId (λ id s => { s with nextRappId := id })

instance (priority := low) : MonadStateOf ActiveGoalQueue SearchM :=
  MonadStateOf.ofLens State.activeGoals (λ x s => { s with activeGoals := x })

protected def run (ctx : Context) (state : State) (x : SearchM α) :
    MetaM (α × State) :=
  StateRefT'.run (ReaderT.run x ctx) state

protected def run' (ctx : Context) (state : State) (x : SearchM α) :
    MetaM α :=
  return (← SearchM.run ctx state x).fst

end SearchM

def readMainGoal : SearchM MVarId :=
  Context.mainGoal <$> read

def readRootGoal : SearchM GoalRef :=
  Context.rootGoal <$> read

def getAndIncrementNextGoalId : SearchM GoalId := do
  let id ← getThe GoalId
  setThe GoalId id.succ
  return id

def getAndIncrementNextRappId : SearchM RappId := do
  let id ← getThe RappId
  setThe RappId id.succ
  return id

-- Overwrites the goal ID from `g`.
-- TODO refactor: don't take GoalData as arg?
def addGoal (g : GoalData) (parent : RappRef) : SearchM GoalRef := do
  let id ← getAndIncrementNextGoalId
  let g := { g with id := id }
  let gref ← ST.mkRef $ Goal.mk (some parent) #[] g
  parent.modify λ r => r.addChild gref
  modifyThe ActiveGoalQueue λ q => q.insert
    { goal := gref
      successProbability := g.successProbability }
  modify λ s => { s with numGoals := s.numGoals + 1 }
  return gref

def addGoals (goals : Array GoalData) (parent : RappRef) :
    SearchM (Array GoalRef) := do
  let mut grefs := #[]
  for goal in goals do
    let gref ← addGoal goal parent
    grefs := grefs.push gref
  return grefs

def addGoals' (goals : Array MVarId) (successProbability : Percent)
    (parent : RappRef) : SearchM (Array GoalRef) := do
  let goals ← goals.mapM λ g =>
    GoalData.mkInitial GoalId.dummy g successProbability
  addGoals goals parent

-- Overwrites the rapp ID and depth of `r`. Adds the `newUnificationGoals` as
-- unification goals whose origin is the returned rapp.
-- TODO refactor: don't take RappData as arg
def addRapp (r : RappData) (parent : GoalRef)
    (newUnificationGoals : Array MVarId) : SearchM RappRef := do
  let id ← getAndIncrementNextRappId
  let r := r.setId id
  let depth := (← (← parent.get).parentDepth) + 1
  let r := r.setDepth depth
  let rref ← ST.mkRef $ Rapp.mk (some parent) #[] r
  let mut unificationGoalOrigins := r.unificationGoalOrigins
  for goal in newUnificationGoals do
    unificationGoalOrigins := unificationGoalOrigins.insert goal rref
  rref.modify λ r => r.setUnificationGoalOrigins unificationGoalOrigins
  parent.modify λ g => g.addChild rref
  modify λ s => { s with numRapps := s.numRapps + 1 }
  return rref

def runRuleTac' (goal : MVarId) (rule : RuleTac) : MetaM RuleTacOutput :=
  withMVarContext goal $ rule { goal := goal }

def runRuleTac (goal : Goal) (rule : RuleTac) :
    SearchM (Option (RuleTacOutput × Meta.SavedState)) := do
  let (result, finalState) ← goal.runMetaMInParentState $ observing? $
    runRuleTac' goal.goal rule
  return result.map (·, finalState)

def runNormRule (goal : MVarId) (r : NormRule) : MetaM (Option MVarId) := do
  let ruleOutput ←
    try runRuleTac' goal r.tac.tac
    catch e => throwError
      m!"aesop: normalization rule {r.name} failed with error:\n  {e.toMessageData}\nIt was run on this goal:" ++
      MessageData.node #[MessageData.ofGoal goal]
  unless ruleOutput.unificationGoals.isEmpty do
    throwError
      m!"aesop: normalization rule {r.name} produced a metavariable when run on this goal:" ++
      MessageData.node #[MessageData.ofGoal goal]
  match ruleOutput.regularGoals with
  | #[] => return none
  | #[g] => return some g
  | _ => throwError
    m!"aesop: normalization rule {r.name} produced more than one subgoal when run on this goal:{indentD $ MessageData.ofGoal goal}"

def runNormalizationSimp (goal : MVarId) (ctx : Simp.Context) :
    MetaM (Option MVarId) := do
  let (some goal) ← simpAll goal ctx | return none
  return some goal

def runNormRules (goal : MVarId) (rules : Array NormRule) :
    MetaM (Option MVarId) := do
  let mut goal := goal
  for r in rules do
    aesop_trace[stepsNormalization] "Running {r}"
    let (some goal') ← runNormRule goal r | return none
    goal := goal'
    aesop_trace[stepsNormalization] "Goal after {r}:{indentD $ MessageData.ofGoal goal}"
  return goal

def normalizeGoalMVar (rs : RuleSet) (goal : MVarId) : MetaM (Option MVarId) := do
  let rules ← rs.applicableNormalizationRules goal
  let (preSimpRules, postSimpRules) :=
    rules.partition λ r => r.extra.penalty < (0 : Int)
  let (some goal) ← runNormRules goal preSimpRules | return none
  let simpCtx :=
    { (← Simp.Context.mkDefault) with simpLemmas := rs.normSimpLemmas }
  aesop_trace[stepsNormalization] "Running normalization simp"
  let (some goal) ← runNormalizationSimp goal simpCtx | return none
  aesop_trace[stepsNormalization] "Goal after normalization simp:{indentD $ MessageData.ofGoal goal}"
  runNormRules goal postSimpRules

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) : SearchM Bool := do
  let g ← gref.get
  let (false) ← pure g.isNormal | return false
  aesop_trace[steps] "Normalising the goal"
  let rs ← readThe RuleSet
  let newGoal? ← gref.runMetaMModifyingParentState do
    aesop_trace[steps] "Goal before normalisation:{indentD $ MessageData.ofGoal g.goal}"
    let newGoal? ← normalizeGoalMVar rs g.goal
    match newGoal? with
    | some newGoal =>
      aesop_trace[steps] "Goal after normalisation:{indentD $ MessageData.ofGoal newGoal}"
    | none =>
      aesop_trace[steps] "Normalisation solved the goal"
    return newGoal?
  -- TODO check whether normalisation assigned any unification goals
  match newGoal? with
  | some newGoal =>
    let g := g.setGoal newGoal
    let g := g.setNormal true
    gref.set g
    return false
  | none =>
    let g := g.setProofStatus ProofStatus.provenByNormalization
    let g := g.setNormal true
    gref.set g
    -- Propagate the fact that g was proven up the tree. We start with the
    -- parent rule application of g (if any). If we were to start with g,
    -- setProven would set the proof status of g to provenByRuleApplication.
    let (some parentRef) ← g.parent | return true
    RappRef.setProven parentRef
    return true

abbrev UnificationGoals := Array (MVarId × Expr × RappRef)

def assignedUnificationGoals (parent : GoalRef)
    (postRuleState : Meta.SavedState) :
    SearchM UnificationGoals := do
  let uGoalOrigins ← (← parent.get).unificationGoalOrigins
  let (result, _) ← runMetaMInSavedState postRuleState do
    let mut result := #[]
    for (ugoal, rref) in uGoalOrigins do
      let (some e) ← getExprMVarAssignment? ugoal | continue
      result := result.push (ugoal, e, rref)
    pure result
  return result

-- This function is called when a rapp R assigns one or more unification goals.
-- We are given the origins of these unification goals, i.e. the rapps which
-- introduced them, as `unificationGoalOrigins`. These origin rapps must all be
-- ancestors of R, so we can find the one highest up in the tree -- the 'least
-- common ancestor' -- by simply picking the origin with the least ID. This
-- relies on the invariant that the ID of a node is always strictly smaller than
-- the ID of its children.
--
-- `unificationGoalOrigins` must be nonempty
def leastCommonUnificationGoalOrigin (unificationGoals : UnificationGoals) :
    SearchM RappRef := do
  if unificationGoals.isEmpty then
    throwError "aesop/leastCommonUnificationGoalOrigin: internal error: empty unificationGoalOrigins"
  let mut min := unificationGoals.get! 0 |>.snd.snd
  if unificationGoals.size = 1 then
    return min
  let mut minId ← (← min.get).id
  for (_, _, rref) in unificationGoals do
    let id ← (← rref.get).id
    if id < minId then
      minId := id
      min := rref
  return min

def removeUnificationGoals (assigned : UnificationGoals)
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) :
    PersistentHashMap MVarId RappRef := do
  let mut ugo := unificationGoalOrigins
  for (m, _, _) in assigned do
    ugo := ugo.erase m
  return ugo

-- For each pair `(m, e, _)` in `unificationGoals`, assigns `m := e` in the meta
-- state of `rref` and removes `m` from the unification goals of `rref`. If `m`
-- does not exist in that state, the assignment is silently skipped.
def assignUnificationGoalsInRappState (unificationGoals : UnificationGoals)
    (rref : RappRef) : SearchM Unit := do
  rref.modify λ r => r.setUnificationGoalOrigins $
    removeUnificationGoals unificationGoals r.unificationGoalOrigins
  rref.runMetaMModifying do
    for (m, e, _) in unificationGoals do
      if ! (← isDeclaredMVar m) then
        continue
      if (← Check.unificationGoalAssignments.isEnabled) then do
        if (← isExprMVarAssigned m) then throwError
          "aesop/runRegularRule: internal error: unification goal is already assigned"
        unless (← isValidMVarAssignment m e) do throwError
          "aesop/runRegularRule: internal error: assignment of unification goal is type-incorrect"
      assignExprMVar m e

mutual
  -- Runs `assignMetasInRappState unificationGoals` on `root` and all
  -- descendants of `root`.
  partial def assignUnificationGoalsInRappBranch
      (unificationGoals : UnificationGoals) (root : RappRef) : SearchM Unit := do
    assignUnificationGoalsInRappState unificationGoals root
    (← root.get).subgoals.forM
      (assignUnificationGoalsInGoalBranch unificationGoals)

  partial def assignUnificationGoalsInGoalBranch
      (unificationGoals : UnificationGoals) (root : GoalRef) : SearchM Unit := do
    (← root.get).rapps.forM
      (assignUnificationGoalsInRappBranch unificationGoals)
end

def runCopyTreeT (x : TreeCopy.TreeCopyT SearchM α) : SearchM α := do
  let (a, s) ← x.run' (← getThe GoalId) (← getThe RappId)
  setThe GoalId s.nextGoalId
  setThe RappId s.nextRappId
  return a

def copyRappBranch (root : RappRef) : SearchM RappRef := do
  let parent := (← root.get).parent!
  runCopyTreeT $ TreeCopy.copyRappTree parent root

mutual
  partial def addActiveGoalsFromGoalBranch (root : GoalRef) : SearchM Unit := do
      let activeGoal ← ActiveGoal.ofGoalRef root
      modifyThe ActiveGoalQueue λ q => q.insert activeGoal
      (← root.get).rapps.forM addActiveGoalsFromRappBranch

  partial def addActiveGoalsFromRappBranch (root : RappRef) : SearchM Unit := do
    (← root.get).subgoals.forM addActiveGoalsFromGoalBranch
end

-- If a rule assigned one or more unification goals, this function makes the
-- necessary adjustments to the search tree:
--
-- - Copy the branch of the search tree whose root is the rapp that introduced
--   the assigned unification goal. If multiple unification goals were assigned,
--   we take the topmost such rapp, whose branch contains all occurrences of the
--   assigned unification goals.
-- - Insert the new branch into the active goal queue.
-- - In the old branch, propagate the unification goal assignment into the
--   meta state of every rapp.
-- - TODO Mark the new branch as deferred in favour of the old branch.
-- - TODO possibly disallow the ugoal assignment in the whole branch.
--
-- If the rule did not assign any unification goals, this function does nothing.
def processUnificationGoalAssignment (parent : GoalRef)
    (postRuleState : Meta.SavedState) :
    SearchM (PersistentHashMap MVarId RappRef) := do
  let parentUGoalOrigins ← (← parent.get).unificationGoalOrigins
  let assignedUGoals ← assignedUnificationGoals parent postRuleState
  if assignedUGoals.isEmpty then
    return parentUGoalOrigins
  let oldBranchRoot ← leastCommonUnificationGoalOrigin assignedUGoals
  aesop_trace[steps] "Rule assigned unification goals. Copying the branch of rapp {(← oldBranchRoot.get).id}."
  let newBranchRoot ← copyRappBranch oldBranchRoot
  aesop_trace[steps] "The root of the copied branch has ID {(← newBranchRoot.get).id}."
  assignUnificationGoalsInRappBranch assignedUGoals oldBranchRoot
  addActiveGoalsFromRappBranch newBranchRoot
  return removeUnificationGoals assignedUGoals parentUGoalOrigins

inductive RuleResult
| proven
| failed
| succeeded

namespace RuleResult

def isFailed : RuleResult → Bool
  | failed => true
  | _ => false

end RuleResult

def runRegularRule (parentRef : GoalRef) (rule : RegularRule) :
    SearchM RuleResult := do
  let parent ← parentRef.get
  let successProbability :=
    parent.successProbability * rule.successProbability
  let ruleOutput? ← runRuleTac parent rule.tac.tac
  match ruleOutput?  with
  | some (ruleOutput@{ regularGoals := #[], .. }, finalState) => do
    -- Rule succeeded and did not generate subgoals, meaning the parent
    -- node is proved.
    aesop_trace[steps] "Rule succeeded without subgoals. Goal is proven."
    let uGoals ← processUnificationGoalAssignment parentRef finalState
    let r :=
      RappData.mkInitial RappId.dummy 0 finalState uGoals rule successProbability
      |>.setProven true
    let _ ← addRapp r parentRef #[]
    parentRef.setProven
    return RuleResult.proven
  | some (ruleOutput@{ regularGoals := subgoals, .. }, finalState) => do
    -- Rule succeeded and generated subgoals.
    aesop_trace[steps] "Rule succeeded with subgoals."
    let uGoals ← processUnificationGoalAssignment parentRef finalState
    let r :=
      RappData.mkInitial RappId.dummy 0 finalState uGoals rule successProbability
    let rappRef ← addRapp r parentRef ruleOutput.unificationGoals
    let newGoals ← addGoals' subgoals successProbability rappRef
    aesop_trace[steps] do
      let traceMods ← TraceModifiers.get
      let rappMsg ← rappRef.toMessageData traceMods
      let goalsMsg ← MessageData.node <$>
        newGoals.mapM (·.toMessageData traceMods)
      m!"New rapp:{indentD rappMsg}\nNew goals:{goalsMsg}"
      -- TODO compress goal display: many of the things we display are
      -- uninteresting for new goals/rapps
    return RuleResult.succeeded
  | none => do
    -- Rule did not succeed.
    aesop_trace[steps] "Rule failed."
    parentRef.modify λ (g : Goal) => g.setFailedRapps $ rule :: g.failedRapps
    parentRef.setUnprovable
    return RuleResult.failed

def runFirstSafeRule (gref : GoalRef) : SearchM RuleResult := do
  let g ← gref.get
  let (none) ← g.unsafeQueue
    | return RuleResult.failed
    -- If the unsafe rules have been selected, we have already tried all the
    -- safe rules.
  let ruleSet ← readThe RuleSet
  let (rules, _) ← g.runMetaMInParentState $ ruleSet.applicableSafeRules g.goal
  aesop_trace[steps] "Selected safe rules:{MessageData.node $ rules.map toMessageData}"
  aesop_trace[steps] "Trying safe rules"
  let mut result := RuleResult.failed
  for r in rules do
    aesop_trace[steps] "Trying {r}"
    result ← runRegularRule gref $ RegularRule'.safe r
    if result.isFailed then continue else break
  return result

def SafeRule.asUnsafeRule (r : SafeRule) : UnsafeRule where
  name := r.name
  tac := r.tac
  indexingMode := r.indexingMode
  extra := { successProbability := Percent.ninety }

def selectUnsafeRules (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM (List UnsafeRule) := do
  let g ← gref.get
  match g.unsafeQueue with
  | some rules => return rules
  | none => do
    let ruleSet ← readThe RuleSet
    let (unsafeRules, _) ← g.runMetaMInParentState $
      ruleSet.applicableUnsafeRules g.goal
    let rules ←
      if includeSafeRules then
          let (safeRules, _) ← g.runMetaMInParentState $
            ruleSet.applicableSafeRules g.goal
          let rules := safeRules.map (·.asUnsafeRule) ++ unsafeRules
          -- TODO sort combined rules (this currently makes a test case loop)
          -- let rules := rules.qsort (· < ·) -- TODO stable merge for efficiency
          aesop_trace[steps] "Selected unsafe rules (including safe rules treated as unsafe):{MessageData.node $ rules.map toMessageData}"
          pure rules.toList
          -- TODO these toList conversions make me sad. More efficient: treat
          -- the selected unsafe rules as an array and the unsafe queue as a
          -- subarray (or just an index).
      else
        aesop_trace[steps] "Selected unsafe rules:{MessageData.node $ unsafeRules.map toMessageData}"
        pure unsafeRules.toList
    gref.set $ g.setUnsafeQueue rules
    return rules

def runFirstUnsafeRule (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM Bool := do
  let rules ← selectUnsafeRules gref includeSafeRules
  aesop_trace[steps] "Trying unsafe rules"
  let mut result := RuleResult.failed
  let mut remainingRules := rules
  for r in rules do
    aesop_trace[steps] "Trying {r}"
    remainingRules := remainingRules.tail!
    result ← runRegularRule gref (RegularRule'.unsafe r)
    if result.isFailed then continue else break
  gref.modify λ g => g.setUnsafeQueue remainingRules
  aesop_trace[steps] "Remaining unsafe rules:{MessageData.node $ remainingRules.map toMessageData |>.toArray}"
  if result.isFailed && remainingRules.isEmpty then
    aesop_trace[steps] "Goal is unprovable"
    gref.setUnprovable
  return ¬ remainingRules.isEmpty

-- Returns true if the goal should be reinserted into the goal queue.
def expandGoal (gref : GoalRef) : SearchM Bool := do
  let (false) ← normalizeGoalIfNecessary gref |
    -- Goal was already proven by normalisation.
    -- TODO at least in this case, we must make sure that ugoal assignments
    -- are propagated or disallowed.
    return false
  if ← (← gref.get).hasUnificationGoal then
    aesop_trace[steps] "Goal contains unification goals. Treating safe rules as unsafe."
    -- TODO This is a bit of a lie. Currently we only check whether the goal's
    -- parent rapp has unification goals. That doesn't mean any appear in this
    -- specific goal. It would be better to track this more precisely so that
    -- we can treat ugoal-free goals as ugoal-free (which is much more
    -- efficient).
    runFirstUnsafeRule gref (includeSafeRules := true)
  else
    let safeResult ← runFirstSafeRule gref
    if safeResult.isFailed
      then runFirstUnsafeRule gref (includeSafeRules := false)
      else pure false

def expandNextGoal : SearchM Unit := do
  let some (activeGoal, activeGoals) ← pure (← getThe ActiveGoalQueue).removeMin
    | throwError "aesop/expandNextGoal: internal error: no active goals left"
  setThe ActiveGoalQueue activeGoals
  let gref := activeGoal.goal
  let g ← gref.get
  aesop_trace[steps] "Expanding {← g.toMessageData (← TraceModifiers.get)}"
  if g.isProven ∨ g.isUnprovable ∨ g.isIrrelevant then
    aesop_trace[steps] "Skipping goal since it is already proven, unprovable or irrelevant."
    return ()
  let maxRappDepth := (← readThe Aesop.Options).maxRuleApplicationDepth
  if maxRappDepth != 0 && (← (← gref.get).parentDepth) >= maxRappDepth then
    aesop_trace[steps] "Skipping goal since it is beyond the maximum rule application depth."
    gref.modify λ g => g.setUnprovable true
    match (← gref.get).parent with
    | none => pure ()
    | some (rref : RappRef) => rref.setUnprovable
    return ()
  let hasMoreRules ← expandGoal gref
  if hasMoreRules then
    let ag ← ActiveGoal.ofGoalRef gref
    modifyThe ActiveGoalQueue λ q => q.insert ag

mutual
  -- Let g be the goal in gref. Assuming that we are in the meta context of g's
  -- parent and that g was proven by a rule application, this function retrieves
  -- a proof p of g from the first proven rule application and assigns g.goal :=
  -- p.
  --
  -- If g was proven by normalisation, this function does nothing. (g.goal
  -- should then already be assigned to a proof in the meta context of g's
  -- parent.)
  private partial def linkProofsGoal (gref : GoalRef) : MetaM Unit := do
    let g ← gref.get
    match g.proofStatus with
    | ProofStatus.unproven => throwError
      "aesop/linkProofs: internal error: goal {g.id} marked as unproven"
    | ProofStatus.provenByNormalization =>
      return ()
    | ProofStatus.provenByRuleApplication => do
      let (some provenRapp) ← g.firstProvenRapp? | throwError
        "aesop/linkProofs: internal error: goal {g.id} marked as proven but does not have a proven rule application"
      let proof ← linkProofsRapp provenRapp
      if (← isExprMVarAssigned g.goal) then do throwError
        "aesop/linkProofs: internal error: goal metavariable of goal {g.id} already assigned.\nPrevious assignment:{indentExpr (← getExprMVarAssignment? g.goal).get!}"
      let goalMVar := g.goal
      if (← Check.proofReconstruction.isEnabled) then
        withMVarContext goalMVar do
          check proof <|> throwError
            "{Check.proofReconstruction.name}: reconstructed proof of goal {g.id} is type-incorrect"
          let (true) ← isDefEq (← getMVarType goalMVar) (← inferType proof)
            | throwError "{Check.proofReconstruction.name}: reconstructed proof of goal {g.id} has the wrong type"
      assignExprMVar goalMVar proof

  -- Let r be the rapp in rref. This function assigns the goal metavariables of
  -- the subgoals of r (in the meta context of r). Then it returns r's parent
  -- goal with metavariables instantiated. The result is a guaranteed
  -- metavariable-free proof of r's parent goal.
  private partial def linkProofsRapp (rref : RappRef) : MetaM Expr :=
    rref.runMetaMModifying do
      let r ← rref.get
      r.subgoals.forM linkProofsGoal
      let proof ← instantiateMVars $ mkMVar (← r.parent!.get).goal
      if proof.hasMVar then throwError
        "aesop/linkProofs: internal error: proof extracted from rapp {r.id} contains unassigned metavariables"
      return proof
end

-- Let g be the goal in gref. Assuming that g is proven, this function assigns
-- the goal metavariable of g to a proof of g. In the process, various
-- metavariables in the tree are also assigned, so this function can only be
-- called once.
def GoalRef.linkProofs (gref : GoalRef) : MetaM Unit := linkProofsGoal gref

def finishIfProven : SearchM Bool := do
  let root ← readRootGoal
  let (true) ← pure (← root.get).isProven
    | return false
  aesop_trace[steps] "Root node is proven. Linking proofs."
  root.linkProofs
  aesop_trace[proof] do
    let mainGoal ← readMainGoal
    withMVarContext mainGoal $
      m!"Final proof:{indentExpr (← instantiateMVars $ mkMVar mainGoal)}"
  return true

def checkGoalLimit : SearchM Unit := do
  let maxGoals := (← readThe Aesop.Options).maxGoals
  let currentGoals := (← get).numGoals
  if maxGoals != 0 && currentGoals >= maxGoals then throwError
    "aesop: maximum number of goals ({maxGoals}) reached. Set the maxGoals option to increase the limit."

def checkRappLimit : SearchM Unit := do
  let maxRapps := (← readThe Aesop.Options).maxRuleApplications
  let currentRapps := (← get).numRapps
  if maxRapps != 0 && currentRapps >= maxRapps then throwError
    "aesop: maximum number of rule applications ({maxRapps}) reached. Set the maxRuleApplications option to increase the limit."

partial def searchLoop : SearchM Unit := do
  let root ← readRootGoal
  let (false) ← pure (← root.get).isUnprovable
    | throwError "aesop: failed to prove the goal"
  let (false) ← finishIfProven | pure ()
  checkGoalLimit
  checkRappLimit
  expandNextGoal
  aesop_trace[stepsTree] "Current search tree:{indentD (← (← readRootGoal).treeToMessageData (← TraceModifiers.get))}"
  (← readRootGoal).checkInvariantsIfEnabled
  searchLoop

def search (rs : RuleSet) (options : Aesop.Options) (mainGoal : MVarId) :
    MetaM Unit := do
  let (ctx, state) ← mkInitialContextAndState rs options mainGoal
  searchLoop.run' ctx state

def searchTactic (rs : RuleSet) (options : Aesop.Options) : TacticM Unit :=
  liftMetaTactic λ goal => search rs options goal *> pure []

end Aesop
