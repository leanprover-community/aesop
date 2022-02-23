/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

-- TODO If a 'finished' proof contains metavariables, what should we do?

import Aesop.Check
import Aesop.Options
import Aesop.RuleSet
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
  priority : Percent
  lastExpandedInIteration : Iteration
    -- Iteration of the search loop when this goal was last expanded (counting
    -- from 1), or 0 if the goal was never expanded.
  addedInIteration : Iteration
    -- Iteration of the search loop when this goal was added. 0 for the root
    -- goal.

namespace ActiveGoal

-- We prioritise active goals lexicographically by the following criteria:
--
--  1. Goals with higher priority have priority.
--  2. Goals which were last expanded in an earlier iteration have priority.
--  3. Goals which were added in an earlier iteration have priority.
--
-- The last two criteria ensure a very weak form of fairness: if a search
-- produces infinitely many goals with the same success probability, each of
-- them will be expanded infinitely often.
--
-- Note that since we use a min-queue, `le x y` means `x` has priority over `y`.
protected def le (g h : ActiveGoal) : Bool :=
  g.priority > h.priority ||
    (g.priority == h.priority &&
      (g.lastExpandedInIteration <= h.lastExpandedInIteration ||
        (g.lastExpandedInIteration == h.lastExpandedInIteration &&
          g.addedInIteration <= h.addedInIteration)))

protected def ofGoalRef [Monad m] [MonadLiftT (ST IO.RealWorld) m]
    (gref : GoalRef) : m ActiveGoal := do
  let g ← gref.get
  return {
    goal := gref
    priority := g.priority
    lastExpandedInIteration := g.lastExpandedInIteration
    addedInIteration := g.addedInIteration
  }

end ActiveGoal

abbrev ActiveGoalQueue := BinomialHeap ActiveGoal ActiveGoal.le

structure Context where
  ruleSet : RuleSet
  options : Aesop.Options
  mainGoal : MVarId
  rootGoal : GoalRef

structure State where
  activeGoals : ActiveGoalQueue
  nextGoalId : GoalId
  nextRappId : RappId
  iteration : Iteration
  numGoals : Nat
  numRapps : Nat
    -- As currently implemented, we always have numGoals = nextGoalId and
    -- iteration - 1 = nextRappId = numRapps. But these are conceptually
    -- different things, so we should track them separately.

def mkInitialContextAndState (rs : RuleSet) (options : Aesop.Options)
    (mainGoal : MVarId) : MetaM (Context × State) := do
  let ugoals ← getGoalMVarsNoDelayed mainGoal
  unless ugoals.isEmpty do
    throwError "aesop: the goal contains metavariables, which is not currently supported."
    -- TODO support metavariables in the initial goal
  let rootGoal :=
    Goal.mkInitial GoalId.zero none mainGoal HashSet.empty Percent.hundred
      Iteration.none BranchState.empty
  let rootGoalRef ← ST.mkRef rootGoal
  let ctx := {
    ruleSet := rs
    options := options
    mainGoal := mainGoal
    rootGoal := rootGoalRef }
  let state := {
    activeGoals := BinomialHeap.singleton (← ActiveGoal.ofGoalRef rootGoalRef)
    nextGoalId := GoalId.one
    nextRappId := RappId.zero
    iteration := Iteration.one
    numGoals := 1
    numRapps := 0 }
  return (ctx, state)

abbrev SearchM := ReaderT Context $ StateRefT State MetaM

namespace SearchM

instance : Inhabited (SearchM α) where
  default := throwError ""

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

instance (priority := low) : MonadStateOf Iteration SearchM :=
  MonadStateOf.ofLens State.iteration (λ x s => { s with iteration := x })

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

def popActiveGoal : SearchM (Option GoalRef) := do
  let q ← getThe ActiveGoalQueue
  let (some (ag, q)) ← pure q.deleteMin | return none
  setThe ActiveGoalQueue q
  return some ag.goal

def pushActiveGoal (ag : ActiveGoal) : SearchM Unit :=
  modifyThe ActiveGoalQueue (·.insert ag)

-- Overwrites the goal ID from `g`.
def addGoal (g : Goal) : SearchM GoalRef := do
  let id ← getAndIncrementNextGoalId
  let g := g.setId id
  let gref ← ST.mkRef g
  match g.parent? with
  | none => throwError "aesop: internal error: addGoal expected the goal to have a parent"
  | some parent => parent.modify λ r => r.addChild gref
  pushActiveGoal (← ActiveGoal.ofGoalRef gref)
  modify λ s => { s with numGoals := s.numGoals + 1 }
  return gref

def addGoals (goals : Array Goal) (parent : RappRef) :
    SearchM (Array GoalRef) :=
  goals.mapM addGoal

def addGoals' (goals : Array (MVarId × HashSet MVarId))
    (successProbability : Percent) (parent : RappRef)
    (branchState : BranchState) : SearchM (Array GoalRef) := do
  let i ← getThe Iteration
  goals.mapM λ (g, ugoals) => addGoal $
    Goal.mkInitial GoalId.dummy (some parent) g ugoals successProbability i
      branchState

-- Overwrites the rapp ID and depth of `r`. Adds the `newUnificationGoals` as
-- unification goals whose origin is the returned rapp.
def addRapp (r : Rapp) (newUnificationGoals : HashSet MVarId) :
    SearchM RappRef := do
  let id ← getAndIncrementNextRappId
  let r := r.setId id
  let depth := (← (← r.parent.get).parentDepth) + 1
  let r := r.setDepth depth
  let rref ← ST.mkRef r
  let mut unificationGoalOrigins := r.unificationGoalOrigins
  for goal in newUnificationGoals do
    unificationGoalOrigins := unificationGoalOrigins.insert goal rref
  rref.modify λ r => r.setUnificationGoalOrigins unificationGoalOrigins
  r.parent.modify λ g => g.addChild rref
  modify λ s => { s with numRapps := s.numRapps + 1 }
  return rref

def runRuleTac (goal : Goal) (rule : RuleTac)
    (indexMatchLocations : Array IndexMatchLocation)
    (branchState : Option RuleBranchState) :
    MetaM (Sum Exception RuleTacOutput) := do
  try
    let (result, _) ← goal.runMetaMInParentState $ rule
      { goal := goal.goal
        indexMatchLocations := indexMatchLocations
        branchState? := branchState }
    return Sum.inr result
  catch e =>
    return Sum.inl e

-- NOTE: Must be run in the MetaM context after the rule has been run.
def checkProducedUGoals (rule : Rule' α τ)
    (goals : Array (MVarId × HashSet MVarId)) : MetaM Unit := do
  for (goal, reportedUGoals) in goals do
    let actualUGoals ← getGoalMVarsNoDelayed goal
    if actualUGoals != reportedUGoals then throwError
      "{Check.rules.name}: rule {rule.name} reported wrong unification goals"
    if reportedUGoals.contains goal then throwError
      "{Check.rules.name}: rule {rule.name} reported goal {goal.name} as both a regular and unification goal"

def checkRuleApplication (rule : Rule' α τ) (rapp : RuleApplication) :
    MetaM Unit :=
  discard $ runMetaMInSavedState rapp.postState $
    checkProducedUGoals rule rapp.goals

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRuleTac (bs : BranchState)
    (ugoalOrigins : PersistentHashMap MVarId RappRef) (rule : NormRule)
    (ri : RuleTacInput) :
    MetaM (Option (MVarId × BranchState)) := do
  let mut previouslyAssignedUgoals := HashSet.empty
  if ← Check.rules.isEnabled then
    for (ugoal, _) in ugoalOrigins do
      if ← isExprMVarAssigned ugoal then
        previouslyAssignedUgoals := previouslyAssignedUgoals.insert ugoal

  let result ←
    try rule.tac.tac ri
    catch e => throwError
      "aesop: normalisation rule {rule.name} failed with error:{indentD e.toMessageData}\n{Thunk.get errorContext}"

  let postBranchState := bs.update rule result.postBranchState?
  match result.applications with
  | #[ruleOutput] =>
    match ruleOutput.goals with
    | #[] => return none
    | #[(g, ugoals)] =>
      if ← Check.rules.isEnabled then
        checkProducedUGoals rule ruleOutput.goals
        for ugoal in ugoals do
          unless ugoalOrigins.contains ugoal do throwError
            "{Check.rules.name}: normalisation rule {rule.name} introduced a new unification goal. {Thunk.get errorContext}"
        for (ugoal, _) in ugoalOrigins do
          if ! (← pure (previouslyAssignedUgoals.contains ugoal) <&&> isExprMVarAssigned ugoal) then throwError
            "{Check.rules.name}: normalisation rule {rule.name} assigned a unification goal. {Thunk.get errorContext}"
      return some (g, postBranchState)
    | _ => throwError
      "aesop: normalisation rule {rule.name} produced more than one subgoal. {Thunk.get errorContext}"
  | _ => throwError
    "aesop: normalisation rule {rule.name} did not produce exactly one rule application. {Thunk.get errorContext}"
  where
    errorContext : Thunk MessageData :=
      m!"It was run on this goal:{indentD $ MessageData.ofGoal ri.goal}"

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRule (goal : MVarId) (branchState : BranchState)
    (ugoalOrigins : PersistentHashMap MVarId RappRef)
    (rule : IndexMatchResult NormRule) :
    MetaM (Option (MVarId × BranchState)) := do
  aesop_trace[stepsNormalization] "Running {rule.rule}"
  let ruleInput := {
    goal := goal
    indexMatchLocations := rule.matchLocations
    branchState? := branchState.find? rule.rule
  }
  let result ← runNormRuleTac branchState ugoalOrigins rule.rule ruleInput
  match result with
  | none => return none
  | some result@(newGoal, _) =>
    aesop_trace[stepsNormalization] "Goal after {rule.rule}:{indentD $ MessageData.ofGoal newGoal}"
    return some result

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRules (goal : MVarId) (branchState : BranchState)
    (ugoalOrigins : PersistentHashMap MVarId RappRef)
    (rules : Array (IndexMatchResult NormRule)) :
    MetaM (Option (MVarId × BranchState)) := do
  let mut goal := goal
  let mut branchState := branchState
  for rule in rules do
    let (some (g, bs)) ← runNormRule goal branchState ugoalOrigins rule
      | return none
    goal := g
    branchState := branchState
  return some (goal, branchState)

def runNormalizationSimp (goal : MVarId) (rs : RuleSet) :
    MetaM (Option MVarId) := do
  let simpCtx :=
    { (← Simp.Context.mkDefault) with simpTheorems := rs.normSimpLemmas }
    -- TODO This computation should be done once, not every time we normalise
    -- a goal.
  let goal? ← simpAll goal simpCtx
  goal?.mapM λ goal => Prod.snd <$> intros goal

-- NOTE: Must be run in the MetaM context of the relevant goal.
def normalizeGoalMVar (rs : RuleSet) (goal : MVarId)
    (branchState : BranchState)
    (ugoalOrigins : PersistentHashMap MVarId RappRef) :
    MetaM (Option (MVarId × BranchState)) := do
  let rules ← rs.applicableNormalizationRules goal
  let (preSimpRules, postSimpRules) :=
    rules.partition λ r => r.rule.extra.penalty < (0 : Int)
  let (some (goal, branchState)) ←
    runNormRules goal branchState ugoalOrigins preSimpRules
    | return none
  aesop_trace[stepsNormalization] "Running normalisation simp"
  let (some goal) ← runNormalizationSimp goal rs | return none
  aesop_trace[stepsNormalization] "Goal after normalisation simp:{indentD $ MessageData.ofGoal goal}"
  runNormRules goal branchState ugoalOrigins postSimpRules

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) : SearchM Bool := do
  let g ← gref.get
  if g.isNormal then
    return false
  aesop_trace[steps] "Normalising the goal"
  let rs ← readThe RuleSet
  let newGoal? ← gref.runMetaMModifyingParentState do
    aesop_trace[steps] "Goal before normalisation:{indentD $ MessageData.ofGoal g.goal}"
    let newGoal? ←
      normalizeGoalMVar rs g.goal g.branchState (← g.unificationGoalOrigins)
    match newGoal? with
    | some (newGoal, _) =>
      aesop_trace[steps] "Goal after normalisation:{indentD $ MessageData.ofGoal newGoal}"
    | none =>
      aesop_trace[steps] "Normalisation solved the goal"
    return newGoal?
  -- The double match on newGoal? is not redundant: above, we operate in the
  -- MetaM state of the goal; below, in the global MetaM state.
  match newGoal? with
  | some (newGoal, newBranchState) =>
    let g := g.setGoal newGoal
    let g := g.setNormal true
    let g := g.setBranchState newBranchState
    gref.set g
    return false
  | none =>
    gref.modify λ g => g.setNormal true
    gref.setProvenByNormalization
    return true
  -- FIXME check whether normalisation assigned any unification goals

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
-- We are given these unification goals, along with their assignments and the
-- rapps that introduced them, as `unificationGoals`. The origin rapps must all
-- be ancestors of R, so we can find the one highest up in the tree -- the
-- 'least common ancestor' -- by simply picking the origin with the least ID.
-- This relies on the invariant that the ID of a node is always strictly smaller
-- than the ID of its children.
--
-- `unificationGoals` must be nonempty
def leastCommonUnificationGoalOrigin (unificationGoals : UnificationGoals) :
    SearchM RappRef := do
  if unificationGoals.isEmpty then
    throwError "aesop/leastCommonUnificationGoalOrigin: internal error: empty unificationGoalOrigins"
  let mut min := unificationGoals[0].snd.snd
  if unificationGoals.size = 1 then
    return min
  let mut minId := (← min.get).id
  for (_, _, rref) in unificationGoals do
    let id := (← rref.get).id
    if id < minId then
      minId := id
      min := rref
  return min

def removeUnificationGoals (assigned : UnificationGoals)
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) :
    PersistentHashMap MVarId RappRef :=
  assigned.foldl (init := unificationGoalOrigins) λ ugo (m, _, _) => ugo.erase m

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
        if (← isExprMVarAssigned m) then do throwError
          "aesop/runRegularRule: internal error: while assigning unification goal {m.name} in rapp {(← rref.get).id}: unification goal is already assigned"
        unless (← isValidMVarAssignment m e) do throwError
          "aesop/runRegularRule: internal error: while assigning unification goal {m.name} in rapp {(← rref.get).id}: assignment is type-incorrect"
      assignExprMVar m e

def removeUnificationGoalsFromGoal (unificationGoals : UnificationGoals)
    (gref : GoalRef) : SearchM Unit := do
  let g ← gref.get
  -- Drop the reference from `g` to make sure that `g.unificationGoals` is not
  -- shared.
  gref.modify λ g => g.setUnificationGoals default
  let mut ugoals := g.unificationGoals
  for (ugoal, _, _) in unificationGoals do
    ugoals := ugoals.erase ugoal
  gref.modify λ g => g.setUnificationGoals ugoals

mutual
  -- Runs `assignMetasInRappState unificationGoals` on `root` and all
  -- descendant rapps of `root`, and `removeUnificationGoalsFromGoal` on the
  -- descendant goals of `root`.
  partial def assignUnificationGoalsInRappBranch
      (unificationGoals : UnificationGoals) (root : RappRef) : SearchM Unit := do
    assignUnificationGoalsInRappState unificationGoals root
    (← root.get).children.forM
      (assignUnificationGoalsInGoalBranch unificationGoals)

  partial def assignUnificationGoalsInGoalBranch
      (unificationGoals : UnificationGoals) (root : GoalRef) : SearchM Unit := do
    removeUnificationGoalsFromGoal unificationGoals root
    (← root.get).children.forM
      (assignUnificationGoalsInRappBranch unificationGoals)
end

def runCopyTreeT (afterAddGoal : GoalRef → GoalRef → SearchM Unit)
    (afterAddRapp : RappRef → RappRef → SearchM Unit)
    (x : TreeCopy.TreeCopyT SearchM α) :
    SearchM (α × TreeCopy.State) := do
  let res@(a, s) ←
    x.run' afterAddGoal afterAddRapp (← getThe GoalId) (← getThe RappId)
  setThe GoalId s.nextGoalId
  setThe RappId s.nextRappId
  return res

def copyRappBranch (root : RappRef) : SearchM (RappRef × TreeCopy.State) := do
  let currentIteration ← getThe Iteration
  let afterAddGoal (oldGref : GoalRef) (newGref : GoalRef) : SearchM Unit := do
        newGref.modify λ g =>
          g.setAddedInIteration currentIteration
          |>.setLastExpandedInIteration Iteration.none
        pushActiveGoal (← ActiveGoal.ofGoalRef newGref)
  let parent := (← root.get).parent
  runCopyTreeT afterAddGoal (λ _ _ => pure ()) $
    TreeCopy.copyRappTree parent root

inductive UGoalAssignmentResult
  | noneAssigned
  | assigned
      (newUnificationGoalOrigins : PersistentHashMap MVarId RappRef)
      (copyOfParentGoal : GoalRef)
  deriving Inhabited

namespace UGoalAssignmentResult

def newUnificationGoalOrigins (parent : GoalRef) : UGoalAssignmentResult →
    MetaM (PersistentHashMap MVarId RappRef)
  | noneAssigned => do (← parent.get).unificationGoalOrigins
  | assigned u .. => pure u

def newParentGoal (parent : GoalRef) : UGoalAssignmentResult → GoalRef
  | noneAssigned => parent
  | assigned _ copy => copy

end UGoalAssignmentResult

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
-- - TODO possibly disallow the ugoal assignment in the whole branch.
--
-- If the rule did not assign any unification goals, this function does nothing.
-- If the rule did assign unification goals, it returns:
--
-- - The unification goal origins for the new rapp to be added to the branch.
--   These are the unification goal origins of `parent` minus the assigned
--   unification goals.
-- - The goal corresponding to `parent` in the new branch.
def processUnificationGoalAssignment (parent : GoalRef)
    (postRuleState : Meta.SavedState) :
    SearchM UGoalAssignmentResult := do
  let parentUGoalOrigins ← (← parent.get).unificationGoalOrigins
  let assignedUGoals ← assignedUnificationGoals parent postRuleState
  if assignedUGoals.isEmpty then
    return UGoalAssignmentResult.noneAssigned
  let oldBranchRoot ← leastCommonUnificationGoalOrigin assignedUGoals
  aesop_trace[steps] "Rule assigned unification goals. Copying the branch of rapp {(← oldBranchRoot.get).id}."
  let (newBranchRoot, { goalMap := goalMap, .. }) ← copyRappBranch oldBranchRoot
  aesop_trace[steps] "The root of the copied branch is rapp {(← newBranchRoot.get).id}."
  assignUnificationGoalsInRappBranch assignedUGoals oldBranchRoot
  let newUGoals := removeUnificationGoals assignedUGoals parentUGoalOrigins
  return UGoalAssignmentResult.assigned newUGoals
    (goalMap.find! (← parent.get).id)

inductive RuleResult
| proven
| failed
| succeeded

namespace RuleResult

def isSuccessful : RuleResult → Bool
  | proven => true
  | failed => false
  | succeeded => true

def isFailed (r : RuleResult) : Bool :=
  ! r.isSuccessful

def isProven : RuleResult → Bool
  | proven => true
  | failed => false
  | succeeded => false

end RuleResult

def runRegularRule (parentRef : GoalRef) (rule : RegularRule)
    (indexMatchLocations : Array IndexMatchLocation) :
    SearchM RuleResult := do
  let parent ← parentRef.get
  let successProbability := parent.successProbability * rule.successProbability
  let initialBranchState := rule.withRule λ r => parent.branchState.find? r
  aesop_trace[stepsBranchStates] "Initial branch state: {initialBranchState}"
  let ruleOutput? ←
    runRuleTac parent rule.tac.tac indexMatchLocations initialBranchState
  match ruleOutput? with
  | Sum.inl exc => onFailure exc
  | Sum.inr { applications := #[], .. } => do
    onFailure $ Exception.error (← getRef) "Rule returned no rule applications."
  | Sum.inr output =>
    let rapps := output.applications
    aesop_trace[steps] "Rule succeeded, producing {rapps.size} rule application(s)."
    if ← Check.rules.isEnabled then
      rule.withRule λ r => rapps.forM $ λ rapp => checkRuleApplication r rapp
    let postBranchState :=
      rule.withRule λ r => parent.branchState.update r output.postBranchState?
    aesop_trace[stepsBranchStates] "Updated branch state: {rule.withRule λ r => postBranchState.find? r}"
    match rapps.find? (·.goals.isEmpty) with
    | none =>
      if rule.isSafe then
        aesop_trace[steps] "Goal becomes inactive after a successful safe rule application."
        parentRef.modify λ parent => parent.setState GoalState.inactive
      let mut parentRef := parentRef
      for rapp in rapps do
        parentRef ←
          processRuleApplicationWithSubgoals parentRef rule successProbability
            rapp postBranchState
      return RuleResult.succeeded
    | some proof =>
      aesop_trace[steps] "One of the rule applications has no subgoals. Goal is proven."
      let res ← processUnificationGoalAssignment parentRef proof.postState
      let ugoals ← res.newUnificationGoalOrigins parentRef
      let r :=
        Rapp.mkInitial RappId.dummy parentRef 0 proof.postState ugoals
          rule successProbability
      let rref ← addRapp r HashSet.empty
      rref.setProven (firstRappUnconditional := true)
      aesop_trace[steps]
        "New rapp:{indentD (← rref.toMessageData (← TraceModifiers.get))}"
      return RuleResult.proven
  where
    onFailure (exc : Exception) : SearchM RuleResult := do
      aesop_trace[stepsRuleFailures] "Rule failed with message:{indentD exc.toMessageData}"
      parentRef.modify λ g => g.setFailedRapps $ g.failedRapps.push rule
      return RuleResult.failed

    newUnificationGoals (parentRef : GoalRef)
        (newGoals : Array (MVarId × HashSet MVarId)) : MetaM (HashSet MVarId) := do
      let oldUGoals ← (← parentRef.get).unificationGoalOrigins
      let mut newUGoals := HashSet.empty
      for (_, ugoals) in newGoals do
        for ugoal in ugoals do
          unless oldUGoals.contains ugoal do
            newUGoals := newUGoals.insert ugoal
      return newUGoals

    processRuleApplicationWithSubgoals (parentRef : GoalRef) (rule : RegularRule)
        (successProbability : Percent) (rapp : RuleApplication)
        (postBranchState : BranchState) : SearchM GoalRef := do
      let res ← processUnificationGoalAssignment parentRef rapp.postState
      let r :=
        Rapp.mkInitial RappId.dummy parentRef 0 rapp.postState
          (← res.newUnificationGoalOrigins parentRef) rule successProbability
      let newUGoals ← newUnificationGoals parentRef rapp.goals
      let rref ← addRapp r newUGoals
      let newGoals ←
        addGoals' rapp.goals successProbability rref postBranchState
      aesop_trace[steps] do
        let traceMods ← TraceModifiers.get
        let rappMsg ← rref.toMessageData traceMods
        let goalsMsg := MessageData.node
          (← newGoals.mapM (·.toMessageData traceMods))
        aesop_trace![steps] "New rapp:{indentD rappMsg}\nNew goals:{goalsMsg}"
        -- TODO compress goal display: many of the things we display are
        -- uninteresting for new goals/rapps
      return res.newParentGoal parentRef

def runFirstSafeRule (gref : GoalRef) : SearchM RuleResult := do
  let g ← gref.get
  if g.unsafeRulesSelected then
    return RuleResult.failed
    -- If the unsafe rules have been selected, we have already tried all the
    -- safe rules.
  let ruleSet ← readThe RuleSet
  let (rules, _) ← g.runMetaMInParentState $ ruleSet.applicableSafeRules g.goal
  aesop_trace[steps] "Selected safe rules:{MessageData.node $ rules.map toMessageData}"
  aesop_trace[steps] "Trying safe rules"
  let mut result := RuleResult.failed
  for r in rules do
    aesop_trace[steps] "Trying {r.rule}"
    result ← runRegularRule gref (RegularRule'.safe r.rule) r.matchLocations
    if result.isSuccessful then break
  return result

def SafeRule.asUnsafeRule (r : SafeRule) : UnsafeRule :=
  { r with extra := { successProbability := Percent.ninety } }

def selectUnsafeRules (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM UnsafeQueue := do
  let g ← gref.get
  match g.unsafeQueue? with
  | some rules => return rules
  | none => do
    let ruleSet ← readThe RuleSet
    let (unsafeRules, _) ← g.runMetaMInParentState $
      ruleSet.applicableUnsafeRules g.goal
    let rules ←
      if includeSafeRules then
          let (safeRules, _) ← g.runMetaMInParentState $
            ruleSet.applicableSafeRules g.goal
          let rules :=
            safeRules.map (λ r => { r with rule := r.rule.asUnsafeRule }) ++
            unsafeRules
          let rules := rules.qsort (· < ·)
            -- TODO stable merge for efficiency
          aesop_trace[steps] "Selected unsafe rules (including safe rules treated as unsafe):{MessageData.node $ rules.map toMessageData}"
          pure rules
      else
        aesop_trace[steps] "Selected unsafe rules:{MessageData.node $ unsafeRules.map toMessageData}"
        pure unsafeRules
    let unsafeQueue := UnsafeQueue.initial rules
    gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
    return unsafeQueue

partial def runFirstUnsafeRule (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM Unit := do
  let queue ← selectUnsafeRules gref includeSafeRules
  aesop_trace[steps] "Trying unsafe rules"
  let (remainingQueue, result) ← loop queue
  gref.modify λ g => g.setUnsafeQueue remainingQueue
  aesop_trace[steps] "Remaining unsafe rules:{MessageData.node $ remainingQueue.toArray.map toMessageData}"
  if remainingQueue.isEmpty then
    if (← gref.get).state.isProven then
      pure ()
    else if ← (← gref.get).isUnprovableNoCache then
      aesop_trace[steps] "Goal is unprovable."
      gref.setUnprovable (firstGoalUnconditional := true)
    else
      aesop_trace[steps] "All rules applied, goal becomes inactive."
      gref.modify λ g => g.setState GoalState.inactive
  where
    loop (queue : UnsafeQueue) : SearchM (UnsafeQueue × RuleResult) := do
      let (some (r, queue)) := queue.pop? |
        return (queue, RuleResult.failed)
      aesop_trace[steps] "Trying {r.rule}"
      let result ←
        runRegularRule gref (RegularRule'.unsafe r.rule) r.matchLocations
      if result.isSuccessful
        then return (queue, result)
        else loop queue

def expandGoal (gref : GoalRef) : SearchM Unit := do
  if ← normalizeGoalIfNecessary gref then
    -- Goal was already proven by normalisation.
    return
  if (← gref.get).hasUnificationGoal then
    aesop_trace[steps] "Goal contains unification goals. Treating safe rules as unsafe."
    runFirstUnsafeRule gref (includeSafeRules := true)
  else
    let safeResult ← runFirstSafeRule gref
    if safeResult.isFailed then
      runFirstUnsafeRule gref (includeSafeRules := false)

def expandNextGoal : SearchM Unit := do
  let some gref ← popActiveGoal
    | throwError "aesop/expandNextGoal: internal error: no active goals left"
  aesop_trace[steps] "Expanding {← (← gref.get).toMessageData (← TraceModifiers.get)}"
  if ¬ (← gref.get).state.isActive then
    aesop_trace[steps] "Skipping inactive goal."
    return ()
  let maxRappDepth := (← readThe Aesop.Options).maxRuleApplicationDepth
  if maxRappDepth != 0 && (← (← gref.get).parentDepth) >= maxRappDepth then
    aesop_trace[steps] "Skipping goal since it is beyond the maximum rule application depth."
    gref.setUnprovableUnconditionallyAndSetDescendantsIrrelevant
    return ()
  let currentIteration ← getThe Iteration
  expandGoal gref
  gref.modify λ g => g.setLastExpandedInIteration currentIteration
  if (← gref.get).state.isActive then
    pushActiveGoal (← ActiveGoal.ofGoalRef gref)

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
    match g.state with
    | GoalState.provenByNormalization =>
      return ()
    | GoalState.provenByRuleApplication => do
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
          unless ← isDefEq (← getMVarType goalMVar) (← inferType proof) do
            throwError "{Check.proofReconstruction.name}: reconstructed proof of goal {g.id} has the wrong type"
      assignExprMVar goalMVar proof
    | _ => throwError
      "aesop/linkProofs: internal error: goal {g.id} marked as unproven"

  -- Let r be the rapp in rref. This function assigns the goal metavariables of
  -- the subgoals of r (in the meta context of r). Then it returns r's parent
  -- goal with metavariables instantiated. The result is a guaranteed
  -- metavariable-free proof of r's parent goal.
  private partial def linkProofsRapp (rref : RappRef) : MetaM Expr :=
    rref.runMetaMModifying do
      let r ← rref.get
      r.children.forM linkProofsGoal
      let proof ← instantiateMVars $ mkMVar (← r.parent.get).goal
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
  unless (← root.get).state.isProven do
    return false
  aesop_trace[steps] "Root node is proven. Linking proofs."
  root.linkProofs
  aesop_trace[proof] do
    let mainGoal ← readMainGoal
    withMVarContext mainGoal do
      aesop_trace![proof] "Final proof:{indentExpr (← instantiateMVars $ mkMVar mainGoal)}"
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
  aesop_trace[steps] "=== Search loop iteration {← getThe Iteration}"
  let root ← readRootGoal
  if (← root.get).state.isUnprovable then
    throwError "aesop: failed to prove the goal"
  if ← finishIfProven then
    return ()
  checkGoalLimit
  checkRappLimit
  expandNextGoal
  aesop_trace[stepsTree] "Current search tree:{indentD (← (← readRootGoal).treeToMessageData (← TraceModifiers.get))}"
  aesop_trace[stepsActiveGoalQueue] do
    let traceMods ← TraceModifiers.get
    let activeGoalMsgs ← (← getThe ActiveGoalQueue).toArray.mapM λ ag =>
      ag.goal.toMessageData traceMods
    aesop_trace![stepsActiveGoalQueue] "Current active goals:{MessageData.node activeGoalMsgs}"
  (← readRootGoal).checkInvariantsIfEnabled
  modifyThe Iteration λ i => i.succ
  searchLoop

def search (rs : RuleSet) (options : Aesop.Options) (mainGoal : MVarId) :
    MetaM Unit := do
  let (ctx, state) ← mkInitialContextAndState rs options mainGoal
  try {
    searchLoop.run' ctx state
  } finally {
    ctx.rootGoal.free
  }

def searchTactic (rs : RuleSet) (options : Options) : TacticM Unit :=
  liftMetaTactic λ goal => search rs options goal *> pure []

end Aesop
