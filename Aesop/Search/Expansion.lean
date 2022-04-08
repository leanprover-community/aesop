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
  | postponed (result : PostponedSafeRule)

def RuleResult.isSuccessful
  | proven => true
  | succeeded => true
  | failed => false
  | postponed .. => false


inductive NormRuleResult
  | succeeded (goal : MVarId) (branchState : BranchState)
  | proven
  | failed (err : Exception)

def runRuleTac (tac : RuleTac) (ruleName : RuleName)
    (preState : Meta.SavedState) (input : RuleTacInput) :
    MetaM (Sum Exception RuleTacOutput) := do
  let result ←
    try
      Sum.inr <$> preState.runMetaM' (tac input)
    catch e =>
      return Sum.inl e
  if ← Check.rules.isEnabled then
    if let (Sum.inr ruleOutput) := result then
      ruleOutput.applications.forM λ rapp => do
        if let (some err) ← rapp.check input preState then
          throwError "{Check.rules.name}: while applying rule {ruleName}: {err}"
  return result

def runRegularRuleTac (goal : Goal) (tac : RuleTac) (ruleName : RuleName)
    (indexMatchLocations : Array IndexMatchLocation)
    (branchState : Option RuleBranchState) :
    MetaM (Sum Exception RuleTacOutput) := do
  let some (postNormGoal, postNormState) := goal.postNormGoalAndState? | throwError
    "aesop: internal error: expected goal {goal.id} to be normalised (but not proven by normalisation)."
  let input := {
    goal := postNormGoal
    mvars := goal.mvars
    indexMatchLocations := indexMatchLocations
    branchState? := branchState
  }
  runRuleTac tac ruleName postNormState input

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRuleTac (bs : BranchState) (rule : NormRule) (input : RuleTacInput) :
    MetaM NormRuleResult := do
  let preMetaState ← saveState
  let result? ← runRuleTac rule.tac.tac rule.name preMetaState input
  match result? with
  | Sum.inl e =>
    return NormRuleResult.failed e
  | Sum.inr result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    restoreState rapp.postState
    if rapp.goals.isEmpty then
      return NormRuleResult.proven
    let (#[(g, mvars)]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    unless rapp.introducedMVars.isEmpty do
      err m!"rule introduced additional metavariables"
    let postBranchState := bs.update rule result.postBranchState?
    return NormRuleResult.succeeded g postBranchState
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRule (goal : MVarId) (mvars : Array MVarId) (bs : BranchState)
    (rule : IndexMatchResult NormRule) :
    MetaM NormRuleResult := do
  let branchState? := bs.find? rule.rule
  aesop_trace[stepsNormalization] do
    aesop_trace![stepsNormalization] "Running {rule.rule}"
    if ← TraceOption.stepsBranchStates.isEnabled then
      aesop_trace![stepsNormalization] "Branch state before rule application: {branchState?}"
  let ruleInput := {
    goal, mvars
    indexMatchLocations := rule.matchLocations
    branchState?
  }
  let result ← runNormRuleTac bs rule.rule ruleInput
  aesop_trace[stepsNormalization] do
    match result with
    | NormRuleResult.failed e =>
      aesop_trace![stepsNormalization] "Rule failed with error:{indentD e.toMessageData}"
    | NormRuleResult.succeeded goal bs =>
      aesop_trace![stepsNormalization] "Rule succeeded. New goal:{indentD $ MessageData.ofGoal goal}"
      if ← TraceOption.stepsBranchStates.isEnabled then
        aesop_trace![stepsNormalization] "Branch state after rule application: {bs.find? rule.rule}"
    | NormRuleResult.proven =>
      aesop_trace![stepsNormalization] "Rule proved the goal."
  return result

-- NOTE: Must be run in the MetaM context of the relevant goal.
def runNormRules (goal : MVarId) (mvars : Array MVarId)
    (branchState : BranchState) (rules : Array (IndexMatchResult NormRule)) :
    MetaM (Option (MVarId × BranchState)) := do
  let mut goal := goal
  let mut branchState := branchState
  for rule in rules do
    let result ← runNormRule goal mvars branchState rule
    match result with
    | NormRuleResult.proven => return none
    | NormRuleResult.failed _ => continue
    | NormRuleResult.succeeded g bs =>
      goal := g
      branchState := bs
  return (goal, branchState)

def runNormalizationSimp (goal : MVarId) (rs : RuleSet) :
    MetaM (Option MVarId) := do
  let simpCtx :=
    { (← Simp.Context.mkDefault) with simpTheorems := #[rs.normSimpLemmas] }
    -- TODO This computation should be done once, not every time we normalise
    -- a goal.
  let preMetaState ← saveState
  let newGoal? ← simpAll goal simpCtx
  if ← Check.rules.isEnabled then
    let postMetaState ← saveState
    let introduced :=
      (← introducedExprMVars preMetaState postMetaState).filter (some · != newGoal?)
    unless introduced.isEmpty do
      throwError "{Check.rules.name}: norm simp introduced metas:{introduced.map (·.name)}"
    let assigned :=
      (← assignedExprMVars preMetaState postMetaState).filter (· != goal)
    unless assigned.isEmpty do
      throwError "{Check.rules.name}: norm simp assigned metas:{introduced.map (·.name)}"
  newGoal?.mapM λ goal => Prod.snd <$> intros goal

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

def addRapps (parentRef : GoalRef) (rule : RegularRule)
    (output : RuleTacOutput) : SearchM Q RuleResult := do
  let parent ← parentRef.get
  let rapps := output.applications
  let postBranchState :=
    rule.withRule λ r => parent.branchState.update r output.postBranchState?
  aesop_trace[stepsBranchStates] "Updated branch state: {rule.withRule λ r => postBranchState.find? r}"
  let successProbability := parent.successProbability * rule.successProbability
  let rrefs ← go postBranchState successProbability rapps
  let provenRref? ← rrefs.findM? λ rref => return (← rref.get).state.isProven
  if let (some provenRref) := provenRref? then
    aesop_trace[steps] "One of the rule applications has no subgoals. Goal is proven."
    return RuleResult.proven
  else
    return RuleResult.succeeded
  where
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

    go (postBranchState : BranchState) (successProbability : Percent)
        (rapps : Array RuleApplication) : SearchM Q (Array RappRef) := do
      let parent ← parentRef.get
      let (some (parentGoal, parentMetaState)) := parent.postNormGoalAndState? | throwError
        "aesop: internal error while adding new rapp: expected goal {parent.id} to be normalised (but not proven by normalisation)."
      let rrefs ← rapps.mapM λ rapp => do
        let rref ← addRapp {
          parent := parentRef
          appliedRule := rule
          successProbability
          metaState := rapp.postState
          introducedMVars := rapp.introducedMVars
          assignedMVars := rapp.assignedMVars
          children := rapp.goals.map λ (goal, mvars) =>
            { goal, mvars, branchState := postBranchState }
        }
        (← rref.get).children.forM λ cref => do enqueueGoals (← cref.get).goals
        rref.markProven -- no-op if the rapp is not, in fact, proven
        return rref
      aesop_trace[steps] do traceNewRapps rrefs
      return rrefs

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
    if let (RegularRule'.safe rule) := rule then
      if rapps.any (! ·.assignedMVars.isEmpty) then
        aesop_trace[steps] "Safe rule assigned metavariables. Postponing it."
        return RuleResult.postponed ⟨rule, output⟩
    aesop_trace[steps] "Rule succeeded, producing {rapps.size} rule application(s)."
    addRapps parentRef rule output
  where
    onFailure (msg : MessageData) : SearchM Q RuleResult := do
      aesop_trace[stepsRuleFailures] "Rule failed with message:{indentD msg}"
      parentRef.modify λ g => g.setFailedRapps $ g.failedRapps.push rule
      return RuleResult.failed

def runFirstSafeRule (gref : GoalRef) :
    SearchM Q (RuleResult × Array PostponedSafeRule) := do
  let g ← gref.get
  if g.unsafeRulesSelected then
    return (RuleResult.failed, #[])
    -- If the unsafe rules have been selected, we have already tried all the
    -- safe rules.
  let rules ← selectSafeRules g
  aesop_trace[steps] "Selected safe rules:{MessageData.node $ rules.map toMessageData}"
  aesop_trace[steps] "Trying safe rules"
  let mut postponedRules := {}
  for r in rules do
    aesop_trace[steps] "Trying {r.rule}"
    let result' ←
      runRegularRule gref (RegularRule'.safe r.rule) r.matchLocations
    match result' with
    | RuleResult.failed => continue
    | RuleResult.proven => return (result', #[])
    | RuleResult.succeeded => return (result', #[])
    | RuleResult.postponed r =>
      postponedRules := postponedRules.push r
  return (RuleResult.failed, postponedRules)

partial def runFirstUnsafeRule (postponedSafeRules : Array PostponedSafeRule)
    (parentRef : GoalRef) : SearchM Q Unit := do
  let queue ← selectUnsafeRules postponedSafeRules parentRef
  aesop_trace[steps] "Trying unsafe rules"
  let (remainingQueue, result) ← loop queue
  parentRef.modify λ g => g.setUnsafeQueue remainingQueue
  aesop_trace[steps] "Remaining unsafe rules:{MessageData.node remainingQueue.entriesToMessageData}"
  if remainingQueue.isEmpty then
    if (← parentRef.get).state.isProven then
      return
    if ← (← parentRef.get).isUnprovableNoCache then
      aesop_trace[steps] "Goal is unprovable."
      parentRef.markUnprovable
    else
      aesop_trace[steps] "All rules applied, goal is exhausted."
  where
    loop (queue : UnsafeQueue) : SearchM Q (UnsafeQueue × RuleResult) := do
      let (some (r, queue)) := queue.popFront?
        | return (queue, RuleResult.failed)
      match r with
      | .unsafeRule r =>
        aesop_trace[steps] "Trying {r.rule}"
        let result ←
          runRegularRule parentRef (RegularRule'.unsafe r.rule) r.matchLocations
        match result with
        | RuleResult.proven => return (queue, result)
        | RuleResult.succeeded => return (queue, result)
        | RuleResult.postponed .. => throwError
          "aesop: internal error: applying an unsafe rule yielded a postponed safe rule."
        | RuleResult.failed => loop queue
      | .postponedSafeRule r =>
        aesop_trace[steps] "Applying postponed safe rule {r.rule}"
        let result ←
          addRapps parentRef (RegularRule'.unsafe r.toUnsafeRule) r.output
        return (queue, result)

def expandGoal (gref : GoalRef) : SearchM Q Unit := do
  if ← normalizeGoalIfNecessary gref then
    -- Goal was already proven by normalisation.
    return
  let (safeResult, postponedSafeRules) ← runFirstSafeRule gref
  unless safeResult.isSuccessful do
    runFirstUnsafeRule postponedSafeRules gref

end Aesop
