/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Expansion.Norm

open Lean
open Lean.Meta

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

def runRegularRuleTac (goal : Goal) (tac : RuleTac) (ruleName : RuleName)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation)
    (branchState : RuleBranchState) (options : Options') :
    MetaM (Sum Exception RuleTacOutput) := do
  let some (postNormGoal, postNormState) := goal.postNormGoalAndMetaState? | throwError
    "aesop: internal error: expected goal {goal.id} to be normalised (but not proven by normalisation)."
  let input := {
    goal := postNormGoal
    mvars := goal.mvars
    indexMatchLocations, branchState, options
  }
  runRuleTac tac ruleName postNormState input

def addRapps (parentRef : GoalRef) (rule : RegularRule)
    (rapps : Array RuleApplicationWithMVarInfo)
    (postBranchState? : Option RuleBranchState) : SearchM Q RuleResult := do
  let parent ← parentRef.get
  let postBranchState :=
    rule.withRule λ r => parent.branchState.update r postBranchState?
  aesop_trace[stepsBranchStates] "Updated branch state: {rule.withRule λ r => postBranchState.find? r}"
  let successProbability := parent.successProbability * rule.successProbability

  let mut rrefs := Array.mkEmpty rapps.size
  let mut subgoals := Array.mkEmpty $ rapps.size * 3
  for h : i in [:rapps.size] do
    let rapp := rapps[i]'(by simp_all [Membership.mem])
    let rref ← addRapp {
      rapp with
      parent := parentRef
      appliedRule := rule
      branchState := postBranchState
      successProbability }
    rrefs := rrefs.push rref
    for cref in (← rref.get).children do
      for gref in (← cref.get).goals do
        subgoals := subgoals.push gref

  enqueueGoals subgoals
  rrefs.forM (·.markProven)
    -- `markProven` is a no-op if the rapp is not, in fact, proven. We must
    -- perform this computation after all rapps have been added to ensure
    -- that if one is proven, the others are all marked as irrelevant.

  aesop_trace[steps] do
    let traceMods ← TraceModifiers.get
    let rappMsgs ← rrefs.mapM λ rref => do
      let r ← rref.get
      let rappMsg ← r.toMessageData
      let subgoalMsgs ← r.foldSubgoalsM (init := #[]) λ msgs gref =>
        return msgs.push (← (← gref.get).toMessageData traceMods)
      return rappMsg ++ MessageData.node subgoalMsgs
    aesop_trace![steps] "New rapps and goals:{MessageData.node rappMsgs}"

  let provenRref? ← rrefs.findM? λ rref => return (← rref.get).state.isProven
  if let (some _) := provenRref? then
    aesop_trace[steps] "One of the rule applications has no subgoals. Goal is proven."
    return RuleResult.proven
  else
    return RuleResult.succeeded

def runRegularRuleCore (parentRef : GoalRef) (rule : RegularRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q RuleResult := do
  let parent ← parentRef.get
  let initialBranchState := rule.withRule λ r => parent.branchState.find r
  aesop_trace[stepsBranchStates] "Initial branch state: {initialBranchState}"
  let ruleOutput? ←
    runRegularRuleTac parent rule.tac.run rule.name indexMatchLocations
      initialBranchState (← read).options
  match ruleOutput? with
  | Sum.inl exc => onFailure exc.toMessageData
  | Sum.inr { applications := #[], .. } =>
    onFailure "Rule returned no rule applications."
  | Sum.inr output =>
    let rapps ← output.applications.mapM
      (·.toRuleApplicationWithMVarInfo parent.mvars)
    if let (.safe rule) := rule then
      if rapps.size != 1 then
        return ← onFailure "Safe rule did not produce exactly one rule application. Treating it as failed."
      if rapps.any (! ·.assignedMVars.isEmpty) then
        aesop_trace[steps] "Safe rule assigned metavariables. Postponing it."
        return RuleResult.postponed ⟨rule, output⟩
    aesop_trace[steps] "Rule succeeded, producing {rapps.size} rule application(s)."
    addRapps parentRef rule rapps output.postBranchState?
  where
    onFailure (msg : MessageData) : SearchM Q RuleResult := do
      aesop_trace[stepsRuleFailures] "Rule failed with message:{indentD msg}"
      parentRef.modify λ g => g.setFailedRapps $ g.failedRapps.push rule
      return RuleResult.failed

def runRegularRule (parentRef : GoalRef) (rule : RegularRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q RuleResult :=
  profiling (runRegularRuleCore parentRef rule indexMatchLocations)
    λ result elapsed => do
      let successful :=
        match result with
        | .failed => false
        | .succeeded => true
        | .proven => true
        | .postponed .. => true
      let rule := .ruleName rule.name
      recordAndTraceRuleProfile { rule, elapsed, successful }

-- Never returns `RuleResult.postponed`.
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
      runRegularRule gref (.safe r.rule) r.locations
    match result' with
    | .failed => continue
    | .proven => return (result', #[])
    | .succeeded => return (result', #[])
    | .postponed r =>
      postponedRules := postponedRules.push r
  return (RuleResult.failed, postponedRules)

partial def runFirstUnsafeRule (postponedSafeRules : Array PostponedSafeRule)
    (parentRef : GoalRef) : SearchM Q Unit := do
  let queue ← selectUnsafeRules postponedSafeRules parentRef
  aesop_trace[steps] "Trying unsafe rules"
  let (remainingQueue, _) ← loop queue
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
          runRegularRule parentRef (.«unsafe» r.rule) r.locations
        match result with
        | .proven => return (queue, result)
        | .succeeded => return (queue, result)
        | .postponed .. => throwError
          "aesop: internal error: applying an unsafe rule yielded a postponed safe rule."
        | .failed => loop queue
      | .postponedSafeRule r =>
        aesop_trace[steps] "Applying postponed safe rule {r.rule}"
        let parentMVars := (← parentRef.get).mvars
        let postBranchState? := r.output.postBranchState?
        let rapps ← r.output.applications.mapM
          (·.toRuleApplicationWithMVarInfo parentMVars)
        let result ←
          addRapps parentRef (.«unsafe» r.toUnsafeRule) rapps postBranchState?
        return (queue, result)

def expandGoal (gref : GoalRef) : SearchM Q Unit := do
  if ← normalizeGoalIfNecessary gref then
    -- Goal was already proven by normalisation.
    return
  let (safeResult, postponedSafeRules) ← runFirstSafeRule gref
  unless safeResult.isSuccessful do
    runFirstUnsafeRule postponedSafeRules gref

end Aesop
