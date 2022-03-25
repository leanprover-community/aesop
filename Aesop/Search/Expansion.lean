/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.RuleSelection

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop

variable [Aesop.Queue Q]

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

def runRegularRuleTac (goal : Goal) (rule : RuleTac) (ruleName : RuleName)
    (indexMatchLocations : Array IndexMatchLocation)
    (branchState : Option RuleBranchState) :
    MetaM (Sum Exception RuleTacOutput) := do
  let preMetaState ← saveState
  let result ←
    try
      Sum.inr <$> goal.runMetaMInPostNormState' λ postNormGoal => rule
        { goal := postNormGoal
          mvars := goal.mvars
          indexMatchLocations := indexMatchLocations
          branchState? := branchState }
    catch e =>
      return Sum.inl e
  if ← Check.rules.isEnabled then
    if let (Sum.inr ruleOutput) := result then
      ruleOutput.applications.forM λ (rapp, postMetaState) => do
        if ! (← rapp.introducedMVars.check preMetaState postMetaState) then throwError
          "{Check.rules.name}: while applying rule {ruleName} to goal {goal.id}: rule reported wrong introduced mvars."
  return result

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRuleTac (bs : BranchState) (rule : NormRule) (ri : RuleTacInput) :
    MetaM (Option (MVarId × BranchState)) := do
  let preMetaState ← saveState
  let result ←
    try
      rule.tac.tac ri
    catch e =>
      err m! "rule failed with error:{indentD e.toMessageData}"
  let #[(rapp, postMetaState)] := result.applications
    | err m!"rule did not produce exactly one rule application."
  restoreState postMetaState
  if ← Check.rules.isEnabled <&&>
    notM (rapp.introducedMVars.check preMetaState postMetaState) then
    throwError "{Check.rules.name}: norm rule {rule.name} reported incorrect metavariables."
  let (goals, introducedMVars) ← rapp.introducedMVars.get ri.mvars
  if goals.isEmpty then
    return none
  let (#[(g, mvars)]) := goals
    | err m!"rule produced more than one subgoal."
  unless introducedMVars.isEmpty do
    err m!"rule introduced additional metavariables"
  let postBranchState := bs.update rule result.postBranchState?
  return some (g, postBranchState)
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal ri.goal}"

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRule (goal : MVarId) (mvars : Array MVarId) (branchState : BranchState)
    (rule : IndexMatchResult NormRule) :
    MetaM (Option (MVarId × BranchState)) := do
  aesop_trace[stepsNormalization] "Running {rule.rule}"
  let ruleInput := {
    goal, mvars
    indexMatchLocations := rule.matchLocations
    branchState? := branchState.find? rule.rule
  }
  let result ← runNormRuleTac branchState rule.rule ruleInput
  match result with
  | none => return none
  | some result@(newGoal, _) =>
    aesop_trace[stepsNormalization] "Goal after {rule.rule}:{indentD $ MessageData.ofGoal newGoal}"
    return some result

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRules (goal : MVarId) (mvars : Array MVarId)
    (branchState : BranchState) (rules : Array (IndexMatchResult NormRule)) :
    MetaM (Option (MVarId × BranchState)) := do
  let mut goal := goal
  let mut branchState := branchState
  for rule in rules do
    let (some (g, bs)) ← runNormRule goal mvars branchState rule
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
  let preMetaState ← saveState
  let goal? ← simpAll goal simpCtx
  if ← Check.rules.isEnabled then
    let postMetaState ← saveState
    let introduced :=
      (← introducedExprMVars preMetaState postMetaState).filter (some · != goal?)
    unless introduced.isEmpty do
      throwError "{Check.rules.name}: norm simp introduced metas:{introduced.map (·.name)}"
    let assigned :=
      (← assignedExprMVars preMetaState postMetaState).filter (· != goal)
    unless assigned.isEmpty do
      throwError "{Check.rules.name}: norm simp assigned metas:{introduced.map (·.name)}"
  goal?.mapM λ goal => Prod.snd <$> intros goal

-- NOTE: Must be run in the MetaM context of the relevant goal.
def normalizeGoalMVar (rs : RuleSet) (goal : MVarId) (mvars : Array MVarId)
    (branchState : BranchState) :
    MetaM (Option (MVarId × BranchState)) := do
  let rules ← rs.applicableNormalizationRules goal
  let (preSimpRules, postSimpRules) :=
    rules.partition λ r => r.rule.extra.penalty < (0 : Int)
  let (some (goal, branchState)) ←
    runNormRules goal mvars branchState preSimpRules
    | return none
  aesop_trace[stepsNormalization] "Running normalisation simp"
  let (some goal) ← runNormalizationSimp goal rs | return none
  aesop_trace[stepsNormalization] "Goal after normalisation simp:{indentD $ MessageData.ofGoal goal}"
  runNormRules goal mvars branchState postSimpRules

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) : SearchM Q Bool := do
  let g ← gref.get
  if g.isNormal then
    return false
  aesop_trace[steps] "Normalising the goal"
  let rs := (← read).ruleSet
  let (postGoal?, postState) ← (← gref.get).runMetaMInParentState do
    aesop_trace[steps] "Goal before normalisation:{indentD $ MessageData.ofGoal g.preNormGoal}"
    let postGoal? ← normalizeGoalMVar rs g.preNormGoal g.mvars g.branchState
    if let (some (postGoal, _)) := postGoal? then
      aesop_trace[steps] "Goal after normalisation ({postGoal.name}):{indentD $ toMessageData postGoal}"
      -- This trace needs to happen within the `runMetaMModifyingParentState`
      -- to make sure that the goal is printed correctly.
    return postGoal?
  match postGoal? with
  | some (postGoal, postBranchState) =>
    gref.modify λ g =>
      g.setNormalizationState (NormalizationState.normal postGoal postState)
      |>.setBranchState postBranchState
    return false
  | none =>
    aesop_trace[steps] "Normalisation solved the goal"
    gref.modify λ g =>
      g.setNormalizationState (NormalizationState.provenByNormalization postState)
    gref.markProvenByNormalization
    return true

def runRegularRule (parentRef : GoalRef) (rule : RegularRule)
    (indexMatchLocations : Array IndexMatchLocation) :
    SearchM Q RuleResult := do
  let parent ← parentRef.get
  let initialBranchState := rule.withRule λ r => parent.branchState.find? r
  aesop_trace[stepsBranchStates] "Initial branch state: {initialBranchState}"
  let ruleOutput? ←
    runRegularRuleTac parent rule.tac.tac rule.name indexMatchLocations
      initialBranchState
  match ruleOutput? with
  | Sum.inl exc => onFailure exc.toMessageData
  | Sum.inr { applications := #[], .. } => do
    onFailure $ "Rule returned no rule applications."
  | Sum.inr output =>
    let rapps := output.applications
    aesop_trace[steps] "Rule succeeded, producing {rapps.size} rule application(s)."
    let postBranchState :=
      rule.withRule λ r => parent.branchState.update r output.postBranchState?
    aesop_trace[stepsBranchStates] "Updated branch state: {rule.withRule λ r => postBranchState.find? r}"
    match rapps.find? λ (rapp, _) => rapp.introducedMVars.isEmpty with
    | some rapp =>
      aesop_trace[steps] "One of the rule applications has no subgoals. Goal is proven."
      let #[rref] ← addRapps parent rule.name postBranchState #[rapp]
        | unreachable!
      rref.markProven -- TODO avoid repeated isProvenNoCache check
      return RuleResult.proven
    | none =>
      discard $ addRapps parent rule.name postBranchState rapps
      return RuleResult.succeeded
  where
    onFailure (msg : MessageData) : SearchM Q RuleResult := do
      aesop_trace[stepsRuleFailures] "Rule failed with message:{indentD msg}"
      parentRef.modify λ g => g.setFailedRapps $ g.failedRapps.push rule
      return RuleResult.failed

    -- TODO compress: much of the rapp/goal data is not interesting for new
    -- rapps/goals.
    traceNewRapps (rrefs : Array RappRef) : SearchM Q Unit := do
      let traceMods ← TraceModifiers.get
      let rappMsgs ← rrefs.mapM λ rref => do
        let r ← rref.get
        let rappMsg ← r.toMessageData traceMods
        let subgoalMsgs ← r.foldSubgoalsM (init := #[]) λ msgs gref =>
          return msgs.push (← (← gref.get).toMessageData traceMods)
        return rappMsg ++ MessageData.node subgoalMsgs
      aesop_trace![steps] "New rapps and goals:{MessageData.node rappMsgs}"

    assignedMVars (goalMVars : Array MVarId) (postMetaState : Meta.SavedState) :
        MetaM (HashSet MVarId) :=
      postMetaState.runMetaM' do
        let mut result := {}
        for m in goalMVars do
          if ← isExprMVarAssigned m <||> isDelayedAssigned m then
            result := result.insert m
        return result

    @[inline]
    addRapps (parent : Goal) (ruleName : RuleName)
        (postBranchState : BranchState)
        (rapps : Array (RuleApplication × Meta.SavedState)) :
        SearchM Q (Array RappRef) := do
      let (some (parentGoal, parentMetaState)) := parent.postNormGoalAndState? | throwError
        "aesop: internal error while adding new rapp: expected goal {parent.id} to be normalised (but not proven by normalisation)."
      let successProbability :=
        parent.successProbability * rule.successProbability
      let rrefs ← rapps.mapM λ (rapp, postMetaState) => do
        let (goals, introducedMVars) ←
          postMetaState.runMetaM' $ rapp.introducedMVars.get parent.mvars
        let assignedMVars ←
          match rapp.assignedMVars? with
          | none => assignedMVars parent.mvars postMetaState
          | some x => pure x
        let rref ← addRapp {
          parent := parentRef
          appliedRule := rule
          successProbability
          metaState := postMetaState
          introducedMVars
          assignedMVars
          children := goals.map λ (goal, mvars) =>
            { goal, mvars, branchState := postBranchState }
        }
        (← rref.get).children.forM λ cref => do enqueueGoals (← cref.get).goals
        return rref
      aesop_trace[steps] do traceNewRapps rrefs
      return rrefs

def runFirstSafeRule (gref : GoalRef) : SearchM Q RuleResult := do
  let g ← gref.get
  if g.unsafeRulesSelected then
    return RuleResult.failed
    -- If the unsafe rules have been selected, we have already tried all the
    -- safe rules.
  let rules ← selectSafeRules g
  aesop_trace[steps] "Selected safe rules:{MessageData.node $ rules.map toMessageData}"
  aesop_trace[steps] "Trying safe rules"
  let mut result := RuleResult.failed
  for r in rules do
    aesop_trace[steps] "Trying {r.rule}"
    result ← runRegularRule gref (RegularRule'.safe r.rule) r.matchLocations
    if result.isSuccessful then break
  return result

partial def runFirstUnsafeRule (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM Q Unit := do
  let queue ← selectUnsafeRules gref includeSafeRules
  aesop_trace[steps] "Trying unsafe rules"
  let (remainingQueue, result) ← loop queue
  gref.modify λ g => g.setUnsafeQueue remainingQueue
  aesop_trace[steps] "Remaining unsafe rules:{MessageData.node $ remainingQueue.toArray.map toMessageData}"
  if remainingQueue.isEmpty then
    if (← gref.get).state.isProven then
      return
    if ← (← gref.get).isUnprovableNoCache then
      aesop_trace[steps] "Goal is unprovable."
      gref.markUnprovable
    else
      aesop_trace[steps] "All rules applied, goal is exhausted."
  where
    loop (queue : UnsafeQueue) : SearchM Q (UnsafeQueue × RuleResult) := do
      let (some (r, queue)) := queue.pop?
        | return (queue, RuleResult.failed)
      aesop_trace[steps] "Trying {r.rule}"
      let result ←
        runRegularRule gref (RegularRule'.unsafe r.rule) r.matchLocations
      if result.isSuccessful
        then return (queue, result)
        else loop queue

def expandGoal (gref : GoalRef) : SearchM Q Unit := do
  if ← normalizeGoalIfNecessary gref then
    -- Goal was already proven by normalisation.
    return
  if (← gref.get).hasMVar then
    aesop_trace[steps] "Goal contains metavariables. Treating safe rules as unsafe."
    runFirstUnsafeRule gref (includeSafeRules := true)
  else
    let safeResult ← runFirstSafeRule gref
    if safeResult.isFailed then
      runFirstUnsafeRule gref (includeSafeRules := false)


end Aesop
