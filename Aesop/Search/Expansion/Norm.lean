/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac
import Aesop.Search.Expansion.Basic
import Aesop.Search.Expansion.Simp
import Aesop.Search.RuleSelection
import Aesop.Search.SearchM

open Lean
open Lean.Meta

namespace Aesop

inductive NormRuleResult
  | succeeded (goal : MVarId)
      (scriptStep? : Except DisplayRuleName TacticInvocation)
  | proved (scriptStep? : Except DisplayRuleName TacticInvocation)
  | failed (scriptStep? : Option TacticInvocation)
    -- `simp` may generate a 'dummy' script step even when it fails.

namespace NormRuleResult

def isSuccessful : NormRuleResult → Bool
  | succeeded .. | proved .. => true
  | failed .. => false

def newGoal? : NormRuleResult → Option MVarId
  | succeeded goal .. => goal
  | proved .. | failed .. => none

def toEmoji : NormRuleResult → String
  | succeeded .. => ruleSuccessEmoji
  | proved .. => ruleProvedEmoji
  | failed .. => ruleFailureEmoji

end NormRuleResult

@[inline, always_inline]
def withNormTraceNode (ruleName : DisplayRuleName) (k : MetaM NormRuleResult) :
    MetaM NormRuleResult :=
  withAesopTraceNode .steps fmt do
    let result ← k
    if let some newGoal := result.newGoal? then
      aesop_trace[steps] newGoal
    return result
  where
    fmt (r : Except Exception NormRuleResult) : MetaM MessageData := do
      let emoji := exceptRuleResultToEmoji (·.toEmoji) r
      return m!"{emoji} {ruleName}"

def mkNormRuleTacticInvocation (ruleName : RuleName)
    (scriptBuilder? : Option RuleTacScriptBuilder)
    (preGoal : MVarId) (outGoal? : Option GoalWithMVars)
    (preState postState : Meta.SavedState) :
    MetaM (Except DisplayRuleName TacticInvocation) := do
  let (some scriptBuilder) := scriptBuilder?
    | return .error $ .ruleName ruleName
  try
    let tacticSeq ← scriptBuilder.unstructured.run
    let postGoals := outGoal?.toArray
    return .ok { tacticSeq, preGoal, postGoals, preState, postState }
  catch e =>
    throwError "aesop: error while running script builder for rule {ruleName}:{indentD e.toMessageData}"

def runNormRuleTac (rule : NormRule) (input : RuleTacInput) :
    MetaM NormRuleResult := do
  let preMetaState ← saveState
  let result? ← runRuleTac rule.tac.run rule.name preMetaState input
  match result? with
  | Sum.inl e =>
    aesop_trace[steps] e.toMessageData
    return .failed none
  | Sum.inr result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    restoreState rapp.postState
    if rapp.goals.isEmpty then
      let step? ←
        mkNormRuleTacticInvocation rule.name rapp.scriptBuilder? input.goal none
          preMetaState rapp.postState
      return .proved step?
    let (#[g]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    let mvars := .ofArray input.mvars.toArray
    if ← Check.rules.isEnabled then
      let actualMVars ← rapp.postState.runMetaM' g.getMVarDependencies
      if ! actualMVars == mvars then
         err "the goal produced by the rule depends on different metavariables than the original goal."
    let step? ←
      mkNormRuleTacticInvocation rule.name rapp.scriptBuilder? input.goal
        (some ⟨g, mvars⟩) preMetaState rapp.postState
    return .succeeded g step?
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

def runNormRuleCore (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (options : Options') (rule : IndexMatchResult NormRule) :
    MetaM NormRuleResult := do
  let ruleInput := {
    indexMatchLocations := rule.locations
    goal, mvars, options
  }
  withNormTraceNode (.ruleName rule.rule.name) do
    runNormRuleTac rule.rule ruleInput

def runNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (options : Options') (rule : IndexMatchResult NormRule) :
    ProfileT MetaM NormRuleResult :=
  profiling (runNormRuleCore goal mvars options rule) λ result elapsed =>
    recordRuleProfile {
      elapsed,
      successful := result.isSuccessful
      rule := .ruleName rule.rule.name
    }

def runFirstNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (options : Options') (rules : Array (IndexMatchResult NormRule)) :
    ProfileT MetaM NormRuleResult := do
  for rule in rules do
    let result ← runNormRule goal mvars options rule
    if result.isSuccessful then
      return result
  return .failed none

def mkNormSimpScriptStep (ctx : NormSimpContext)
    (preGoal : MVarId) (postGoal? : Option GoalWithMVars)
    (preState postState : Meta.SavedState) (usedTheorems : Simp.UsedSimps) :
    MetaM TacticInvocation := do
  let tactic ←
    mkNormSimpOnlySyntax preGoal ctx.useHyps ctx.configStx? usedTheorems
  return {
    tacticSeq := #[tactic]
    postGoals := postGoal?.toArray
    preGoal, preState, postState
  }

def SimpResult.toNormRuleResult (ruleName : DisplayRuleName)
    (ctx : NormSimpContext) (originalGoal : GoalWithMVars)
    (preState postState : Meta.SavedState) (generateScript : Bool) :
    SimpResult → MetaM NormRuleResult
  | .unchanged newGoal => do
    let scriptStep? :=
      if generateScript then
        some $ .noop originalGoal.goal ⟨newGoal, originalGoal.mvars⟩ preState
                 postState
      else
        none
    return .failed scriptStep?
  | .solved usedTheorems => do
    let scriptStep? ← mkScriptStep? none usedTheorems
    return .proved scriptStep?
  | .simplified newGoal usedTheorems => do
    let scriptStep? ← mkScriptStep? (some newGoal) usedTheorems
    return .succeeded newGoal scriptStep?
  where
    @[inline, always_inline]
    mkScriptStep? (newGoal? : Option MVarId) (usedTheorems : Simp.UsedSimps) :
        MetaM (Except DisplayRuleName TacticInvocation) := do
      if generateScript then
        let newGoal? := newGoal?.map (⟨·, originalGoal.mvars⟩)
        .ok <$> mkNormSimpScriptStep ctx originalGoal.goal newGoal? preState
                  postState usedTheorems
      else
        return .error ruleName

def normSimpCore (ctx : NormSimpContext)
    (localSimpRules : Array LocalNormSimpRule) (goal : MVarId)
    (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  goal.withContext do
    let preState ← saveState
    let result ←
      if ctx.useHyps then
        Aesop.simpAll goal ctx.toContext (disabledTheorems := {})
      else
        let lctx ← getLCtx
        let mut simpTheorems := ctx.simpTheorems
        for localRule in localSimpRules do
          let (some ldecl) := lctx.findFromUserName? localRule.fvarUserName
            | continue
          let (some simpTheorems') ← observing? $
            simpTheorems.addTheorem (.fvar ldecl.fvarId) ldecl.toExpr
            | continue
          simpTheorems := simpTheorems'
        let ctx := { ctx with simpTheorems }
        Aesop.simpGoalWithAllHypotheses goal ctx
    let postState ← saveState

    -- It can happen that simp 'solves' the goal but leaves some mvars
    -- unassigned. In this case, we treat the goal as unchanged.
    let result ←
      match result with
      | .solved .. =>
        let anyMVarDropped ← goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)
        if anyMVarDropped then
          aesop_trace[steps] "Normalisation simp solved the goal but dropped some metavariables. Skipping normalisation simp."
          restoreState preState
          pure $ .unchanged goal
        else
          pure result
      | .simplified .. =>
        pure result
      | .unchanged .. =>
        aesop_trace[steps] "norm simp left the goal unchanged"
        pure result

    result.toNormRuleResult .normSimp ctx ⟨goal, goalMVars⟩ preState postState
      generateScript

@[inline, always_inline]
def checkSimp (name : String) (mayCloseGoal : Bool) (goal : MVarId)
    (x : MetaM NormRuleResult) : MetaM NormRuleResult := do
  if ! (← Check.rules.isEnabled) then
    x
  else
    let preMetaState ← saveState
    let result ← x
    let newGoal? := result.newGoal?
    let postMetaState ← saveState
    let introduced :=
        (← getIntroducedExprMVars preMetaState postMetaState).filter
        (some · != newGoal?)
    unless introduced.isEmpty do throwError
        "{Check.rules.name}: {name} introduced mvars:{introduced.map (·.name)}"
    let assigned :=
        (← getAssignedExprMVars preMetaState postMetaState).filter (· != goal)
    unless assigned.isEmpty do throwError
        "{Check.rules.name}: {name} assigned mvars:{introduced.map (·.name)}"
    if ← pure (! mayCloseGoal && newGoal?.isNone) <&&> goal.isAssigned then
        throwError "{Check.rules.name}: {name} solved the goal"
    return result

def checkedNormSimpCore (ctx : NormSimpContext)
    (localSimpRules : Array LocalNormSimpRule) (goal : MVarId)
    (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult :=
  checkSimp "norm simp" (mayCloseGoal := true) goal do
    try
      withNormTraceNode .normSimp do
        normSimpCore ctx localSimpRules goal goalMVars generateScript
    catch e =>
      throwError "aesop: error in norm simp: {e.toMessageData}"

def normSimp (ctx : NormSimpContext) (localSimpRules : Array LocalNormSimpRule)
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    ProfileT MetaM NormRuleResult := do
  if ! ctx.enabled then
    aesop_trace[steps] "norm simp is disabled (simp_options := \{ ..., enabled := false })"
    return .failed none
  profiling
    (checkedNormSimpCore ctx localSimpRules goal goalMVars generateScript)
    λ _ elapsed => recordRuleProfile
      { rule := .normSimp, elapsed, successful := true }

def normUnfoldCore (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  let preState ← saveState
  let (result, scriptBuilder?) ←
    unfoldManyStarWithScript goal (unfoldRules.find? ·) generateScript
  let postState ← saveState
  match result with
  | .unchanged =>
    aesop_trace[steps] "nothing to unfold"
    return .failed none
  | .changed newGoal _ =>
    let scriptStep? ← do
      match scriptBuilder? with
      | some unfoldScriptBuilder =>
        pure $ .ok {
          tacticSeq := ← unfoldScriptBuilder.unstructured.run
          preGoal := goal
          postGoals := #[⟨newGoal, goalMVars⟩]
          preState, postState
        }
      | none => pure $ .error .normUnfold
    return .succeeded newGoal scriptStep?

def checkedNormUnfoldCore (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  checkSimp "unfold simp" (mayCloseGoal := false) goal do
    try
      withNormTraceNode .normUnfold do
        normUnfoldCore unfoldRules goal goalMVars generateScript
    catch e =>
      throwError "aesop: error in norm unfold: {e.toMessageData}"

def normUnfold (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    ProfileT MetaM NormRuleResult :=
  profiling (checkedNormUnfoldCore unfoldRules goal goalMVars generateScript)
    λ _ elapsed => recordRuleProfile
      { rule := .normUnfold, elapsed, successful := true }

inductive NormSeqResult where
  | proved (script? : Except DisplayRuleName UnstructuredScript)
  | unproved (goal : MVarId)
      (script? : Except DisplayRuleName UnstructuredScript)

abbrev NormStep :=
  MVarId → Array (IndexMatchResult NormRule) →
  Array (IndexMatchResult NormRule) → ProfileT MetaM NormRuleResult

def runNormSteps (rs : RuleSet) (goal : MVarId) (maxIterations : Nat)
    (steps : Array NormStep) (stepsNe : 0 < steps.size) :
    ProfileT MetaM NormSeqResult := do
  let mut iteration := 0
  let mut step : Fin steps.size := ⟨0, stepsNe⟩
  let mut goal := goal
  let mut script? : Except DisplayRuleName UnstructuredScript := .ok #[]
  let mut preSimpRules := ∅
  let mut postSimpRules := ∅
  while iteration < maxIterations do
    if step.val == 0 then
      let rules ← selectNormRules rs goal
      let (preSimpRules', postSimpRules') :=
        rules.partition λ r => r.rule.extra.penalty < (0 : Int)
      preSimpRules := preSimpRules'
      postSimpRules := postSimpRules'
    match ← steps[step] goal preSimpRules postSimpRules with
    | .succeeded newGoal scriptStep? =>
      goal := newGoal
      script? := return (← script?).push (← scriptStep?)
      iteration := iteration + 1
      step := ⟨0, stepsNe⟩
    | .proved scriptStep? =>
      script? := return (← script?).push (← scriptStep?)
      return .proved script?
    | .failed scriptStep? =>
      script? :=
        match scriptStep? with
        | none => script?
        | some scriptStep => return (← script?).push scriptStep
      if h : step.val + 1 < steps.size then
        step := ⟨step.val + 1, h⟩
      else
        return .unproved goal script?
  throwError "aesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."

def NormStep.runPreSimpRules (options : Options')
    (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, preSimpRules, _ => runFirstNormRule goal mvars options preSimpRules

def NormStep.runPostSimpRules (options : Options')
    (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, _, postSimpRules =>
    runFirstNormRule goal mvars options postSimpRules

def NormStep.unfold (rs : RuleSet) (options : Options')
    (mvars : HashSet MVarId) : NormStep
  | goal, _, _ =>
    normUnfold rs.unfoldRules goal mvars options.generateScript

def NormStep.simp (rs : RuleSet) (ctx : NormSimpContext) (options : Options')
    (mvars : HashSet MVarId) : NormStep
  | goal, _, _ =>
    normSimp ctx rs.localNormSimpLemmas goal mvars options.generateScript

partial def normalizeGoalMVar (rs : RuleSet) (normSimpContext : NormSimpContext)
    (options : Options') (goal : MVarId) (mvars : UnorderedArraySet MVarId) :
    ProfileT MetaM NormSeqResult := do
  let mvarsHashSet := .ofArray mvars.toArray
  let mut normSteps := #[
    NormStep.runPreSimpRules options mvars,
    NormStep.unfold rs options mvarsHashSet,
    NormStep.simp rs normSimpContext options mvarsHashSet,
    NormStep.runPostSimpRules options mvars
  ]
  runNormSteps rs goal options.maxNormIterations normSteps (by simp)

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) [Aesop.Queue Q] :
    SearchM Q Bool := do
  let g ← gref.get
  if ← g.isRoot then
    -- For the root goal, we skip normalization.
    let rootState ← getRootMetaState
    gref.modify λ g =>
      g.setNormalizationState (.normal g.preNormGoal rootState (.ok #[]))
    return false
  match g.normalizationState with
  | .provenByNormalization .. => return true
  | .normal .. => return false
  | .notNormal => pure ()
  let ctx ← read
  let profilingEnabled ← isProfilingEnabled
  let profile ← getThe Profile
  let ((normResult, profile), postState) ←
    (← gref.get).runMetaMInParentState do
      normalizeGoalMVar ctx.ruleSet ctx.normSimpContext ctx.options
        g.preNormGoal g.mvars
      |>.run profilingEnabled profile
  modify λ s => { s with profile }
  match normResult with
  | .unproved postGoal script? =>
    gref.modify (·.setNormalizationState (.normal postGoal postState script?))
    return false
  | .proved script? =>
    gref.modify
      (·.setNormalizationState (.provenByNormalization postState script?))
    gref.markProvenByNormalization
    return true

end Aesop
