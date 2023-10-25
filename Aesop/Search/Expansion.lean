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
  | proved (newRapps : Array RappRef)
  | succeeded (newRapps : Array RappRef)
  | failed

namespace RuleResult

def toEmoji : RuleResult → String
  | proved .. => ruleProvedEmoji
  | succeeded .. => ruleSuccessEmoji
  | failed => ruleFailureEmoji

def isSuccessful
  | proved .. | succeeded .. => true
  | failed => false

end RuleResult

inductive SafeRuleResult
  | regular (result : RuleResult)
  | postponed (result : PostponedSafeRule)

namespace SafeRuleResult

def toEmoji : SafeRuleResult → String
  | regular r => r.toEmoji
  | postponed .. => rulePostponedEmoji

def isSuccessfulOrPostponed
  | regular r => r.isSuccessful
  | postponed .. => true

end SafeRuleResult

def runRegularRuleTac (goal : Goal) (tac : RuleTac) (ruleName : RuleName)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation)
    (options : Options') :
    MetaM (Sum Exception RuleTacOutput) := do
  let some (postNormGoal, postNormState) := goal.postNormGoalAndMetaState? | throwError
    "aesop: internal error: expected goal {goal.id} to be normalised (but not proven by normalisation)."
  let input := {
    goal := postNormGoal
    mvars := goal.mvars
    indexMatchLocations, options
  }
  runRuleTac options tac ruleName postNormState input

def addRapps (parentRef : GoalRef) (rule : RegularRule)
    (rapps : Array RuleApplicationWithMVarInfo) :
    SearchM Q RuleResult := do
  let parent ← parentRef.get

  let mut rrefs := Array.mkEmpty rapps.size
  let mut subgoals := Array.mkEmpty $ rapps.size * 3
  for h : i in [:rapps.size] do
    let rapp := rapps[i]'(by simp_all [Membership.mem])
    let successProbability :=
      parent.successProbability *
      (rapp.successProbability?.getD rule.successProbability)
    let rref ← addRapp {
      rapp with
      parent := parentRef
      appliedRule := rule
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

  let provenRref? ← rrefs.findM? λ rref => return (← rref.get).state.isProven
  if let (some _) := provenRref? then
    return .proved rrefs
  else
    return .succeeded rrefs

private def addRuleFailure (rule : RegularRule) (parentRef : GoalRef) :
    SearchM Q Unit := do
  parentRef.modify λ g => g.setFailedRapps $ g.failedRapps.push rule

@[inline, always_inline]
def withRuleTraceNode (ruleName : RuleName)
    (toEmoji : α → String) (suffix : String) (k : SearchM Q α) : SearchM Q α :=
  withAesopTraceNode .steps fmt k
  where
    fmt (result : Except Exception α) : SearchM Q MessageData := do
      let emoji := exceptRuleResultToEmoji toEmoji result
      return m!"{emoji} {ruleName}{suffix}"

def runRegularRuleCore (parentRef : GoalRef) (rule : RegularRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q (Option RuleTacOutput) := do
  let parent ← parentRef.get
  let ruleOutput? ←
    runRegularRuleTac parent rule.tac.run rule.name indexMatchLocations
      (← read).options
  match ruleOutput? with
  | Sum.inl exc =>
    aesop_trace[steps] exc.toMessageData
    return none
  | Sum.inr { applications := #[], .. } =>
    aesop_trace[steps] "Rule returned no rule applications"
    return none
  | Sum.inr output =>
    return some output

def runSafeRuleCore (parentRef : GoalRef) (rule : SafeRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q SafeRuleResult := do
  withRuleTraceNode rule.name (·.toEmoji) "" do
    let some output ←
        runRegularRuleCore parentRef (.safe rule) indexMatchLocations
      | do addRuleFailure (.safe rule) parentRef; return .regular .failed
    let parentMVars := (← parentRef.get).mvars
    let rapps ←
      output.applications.mapM (·.toRuleApplicationWithMVarInfo parentMVars)
    if rapps.size != 1 then
      aesop_trace[steps] "Safe rule did not produce exactly one rule application"
      addRuleFailure (.safe rule) parentRef
      return .regular .failed
    else if rapps.any (! ·.assignedMVars.isEmpty) then
      aesop_trace[steps] "Safe rule assigned metavariables, so we postpone it"
      return .postponed ⟨rule, output⟩
    else
      return .regular (← addRapps parentRef (.safe rule) rapps)

def runSafeRule (parentRef : GoalRef) (rule : SafeRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q SafeRuleResult :=
  profiling (runSafeRuleCore parentRef rule indexMatchLocations)
    λ result elapsed => recordRuleProfile {
        rule := .ruleName rule.name
        successful := result.isSuccessfulOrPostponed
        elapsed
      }

def runUnsafeRuleCore (parentRef : GoalRef) (rule : UnsafeRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q RuleResult := do
  withRuleTraceNode rule.name (·.toEmoji) "" do
    let some output ←
        runRegularRuleCore parentRef (.unsafe rule) indexMatchLocations
      | do addRuleFailure (.unsafe rule) parentRef; return .failed
    let parentMVars := (← parentRef.get).mvars
    let rapps ←
      output.applications.mapM (·.toRuleApplicationWithMVarInfo parentMVars)
    addRapps parentRef (.unsafe rule) rapps

def runUnsafeRule (parentRef : GoalRef) (rule : UnsafeRule)
    (indexMatchLocations : UnorderedArraySet IndexMatchLocation) :
    SearchM Q RuleResult :=
  profiling (runUnsafeRuleCore parentRef rule indexMatchLocations)
    λ result elapsed => recordRuleProfile {
        rule := .ruleName rule.name
        successful := result.isSuccessful
        elapsed
      }

inductive SafeRulesResult
  | proved (newRapps : Array RappRef)
  | succeeded (newRapps : Array RappRef)
  | failed (postponed : Array PostponedSafeRule)
  | skipped

def SafeRulesResult.toEmoji : SafeRulesResult → String
  | proved .. => ruleProvedEmoji
  | succeeded .. => ruleSuccessEmoji
  | failed .. => ruleFailureEmoji
  | skipped => ruleSkippedEmoji

def runFirstSafeRule (gref : GoalRef) : SearchM Q SafeRulesResult := do
  let g ← gref.get
  if g.unsafeRulesSelected then
    return .skipped
    -- If the unsafe rules have been selected, we have already tried all the
    -- safe rules.
  let rules ← selectSafeRules g
  let mut postponedRules := {}
  for r in rules do
    let result ← runSafeRule gref r.rule r.locations
    match result with
    | .regular .failed => continue
    | .regular (.proved newRapps) => return .proved newRapps
    | .regular (.succeeded newRapps) => return .succeeded newRapps
    | .postponed r =>
      postponedRules := postponedRules.push r
  return .failed postponedRules

def applyPostponedSafeRule (r : PostponedSafeRule) (parentRef : GoalRef) :
    SearchM Q RuleResult := do
  withRuleTraceNode r.rule.name (·.toEmoji) " (postponed)" do
    let parentMVars := (← parentRef.get).mvars
    let rapps ← r.output.applications.mapM
      (·.toRuleApplicationWithMVarInfo parentMVars)
    addRapps parentRef (.«unsafe» r.toUnsafeRule) rapps

partial def runFirstUnsafeRule (postponedSafeRules : Array PostponedSafeRule)
    (parentRef : GoalRef) : SearchM Q RuleResult := do
  let queue ← selectUnsafeRules postponedSafeRules parentRef
  let (remainingQueue, result) ← loop queue
  parentRef.modify λ g => g.setUnsafeQueue remainingQueue
  if remainingQueue.isEmpty then
    let parent ← parentRef.get
    if ← pure (! parent.state.isProven) <&&> parent.isUnprovableNoCache then
      parentRef.markUnprovable
  return result
  where
    loop (queue : UnsafeQueue) : SearchM Q (UnsafeQueue × RuleResult) := do
      let (some (r, queue)) := Subarray.popFront? queue
        | return (queue, RuleResult.failed)
      match r with
      | .unsafeRule r =>
        let result ← runUnsafeRule parentRef r.rule r.locations
        match result with
        | .proved .. => return (queue, result)
        | .succeeded .. => return (queue, result)
        | .failed => loop queue
      | .postponedSafeRule r =>
        return (queue, ← applyPostponedSafeRule r parentRef)

def expandGoal (gref : GoalRef) : SearchM Q RuleResult := do
  let provedByNorm ←
    withAesopTraceNode .steps fmtNorm (normalizeGoalIfNecessary gref)
  aesop_trace[steps] do
    let (goal, metaState) ←
      (← gref.get).currentGoalAndMetaState (← getRootMetaState)
    metaState.runMetaM' do
      aesop_trace![steps] "Goal after normalisation:{indentD goal}"
  if provedByNorm then
    return .proved #[]
  let safeResult ←
    withAesopTraceNode .steps fmtSafe (runFirstSafeRule gref)
  match safeResult with
  | .succeeded newRapps => return .succeeded newRapps
  | .proved newRapps => return .proved newRapps
  | .failed postponedSafeRules => doUnsafe postponedSafeRules
  | .skipped => doUnsafe #[]
  where
    doUnsafe (postponedSafeRules : Array PostponedSafeRule) :
        SearchM Q RuleResult := do
      withAesopTraceNode .steps fmtUnsafe do
        runFirstUnsafeRule postponedSafeRules gref

    fmtNorm (result : Except Exception Bool) : SearchM Q MessageData :=
      let emoji :=
        match result with
        | .error _ => ruleErrorEmoji
        | .ok true => ruleProvedEmoji
        | .ok false => ruleSuccessEmoji
      return m!"{emoji} Normalisation"

    fmtSafe (result : Except Exception SafeRulesResult) :
        SearchM Q MessageData :=
      return m!"{exceptRuleResultToEmoji (·.toEmoji) result} Safe rules"

    fmtUnsafe (result : Except Exception RuleResult) : SearchM Q MessageData :=
      return m!"{exceptRuleResultToEmoji (·.toEmoji) result} Unsafe rules"

end Aesop
