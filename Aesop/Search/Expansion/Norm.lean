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

variable [Aesop.Queue Q]

inductive NormRuleResult
  | succeeded (goal : MVarId) (branchState? : Option BranchState)
      (scriptStep? : Except DisplayRuleName UnstructuredScriptStep)
  | proved (scriptStep? : Except DisplayRuleName UnstructuredScriptStep)
  | failed (scriptStep? : Option UnstructuredScriptStep)
    -- `simp` may generate a 'dummy' script step even when it fails.

def NormRuleResult.isSuccessful : NormRuleResult → Bool
  | succeeded .. | proved .. => true
  | failed .. => false

def NormRuleResult.newGoal? : NormRuleResult → Option MVarId
  | succeeded goal .. => goal
  | proved .. | failed .. => none

def NormRuleResult.newBranchState? : NormRuleResult → Option BranchState
  | succeeded (branchState? := bs) .. => bs
  | proved .. | failed .. => none

def mkNormRuleScriptStep (ruleName : RuleName)
    (scriptBuilder? : Option RuleTacScriptBuilder)
    (inGoal : MVarId) (outGoal? : Option GoalWithMVars) :
    MetaM (Except DisplayRuleName UnstructuredScriptStep) := do
  let (some scriptBuilder) := scriptBuilder?
    | return .error $ .ruleName ruleName
  try
    let tacticSeq ← scriptBuilder.unstructured.run
    let outGoals :=
      match outGoal? with
      | none => #[]
      | some g => #[g]
    return .ok {
      otherSolvedGoals := #[]
      tacticSeq, inGoal, outGoals
    }
  catch e =>
    throwError "aesop: error while running script builder for rule {ruleName}:{indentD e.toMessageData}"

def runNormRuleTac (bs : BranchState) (rule : NormRule) (input : RuleTacInput) :
    MetaM NormRuleResult := do
  let preMetaState ← saveState
  let result? ← runRuleTac rule.tac.run rule.name preMetaState input
  match result? with
  | Sum.inl e =>
    aesop_trace[stepsNormalization] "Rule failed with error:{indentD e.toMessageData}"
    return .failed none
  | Sum.inr result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    restoreState rapp.postState
    if rapp.goals.isEmpty then
      aesop_trace[stepsNormalization] "Rule proved the goal."
      let step? ←
        mkNormRuleScriptStep rule.name rapp.scriptBuilder? input.goal none
      return .proved step?
    let (#[g]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    let postBranchState := bs.update rule result.postBranchState?
    aesop_trace[stepsNormalization] do
      aesop_trace![stepsNormalization] "Rule succeeded. New goal:{indentD $ .ofGoal g}"
      aesop_trace[stepsBranchStates] "Branch state after rule application: {postBranchState.find? rule}"
    let mvars := .ofArray input.mvars.toArray
    if ← Check.rules.isEnabled then
      let actualMVars ← rapp.postState.runMetaM' g.getMVarDependencies
      if ! actualMVars == mvars then
         err "the goal produced by the rule depends on different metavariables than the original goal."
    let step? ←
      mkNormRuleScriptStep rule.name rapp.scriptBuilder? input.goal
        (some ⟨g, mvars⟩)
    return .succeeded g postBranchState step?
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

def runNormRuleCore (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (bs : BranchState) (options : Options') (rule : IndexMatchResult NormRule) :
    MetaM NormRuleResult := do
  let branchState := bs.find rule.rule
  aesop_trace[stepsNormalization] do
    aesop_trace![stepsNormalization] "Running {rule.rule}"
    aesop_trace[stepsBranchStates] "Branch state before rule application: {branchState}"
  let ruleInput := {
    indexMatchLocations := rule.locations
    goal, mvars, branchState, options
  }
  runNormRuleTac bs rule.rule ruleInput

def runNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (bs : BranchState) (options : Options') (rule : IndexMatchResult NormRule) :
    ProfileT MetaM NormRuleResult :=
  profiling (runNormRuleCore goal mvars bs options rule) λ result elapsed => do
    let ruleProfile := {
      elapsed
      successful := result.isSuccessful
      rule := .ruleName rule.rule.name
    }
    recordAndTraceRuleProfile ruleProfile

def runFirstNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (branchState : BranchState) (options : Options')
    (rules : Array (IndexMatchResult NormRule)) :
    ProfileT MetaM NormRuleResult := do
  for rule in rules do
    let result ← runNormRule goal mvars branchState options rule
    if result.isSuccessful then
      return result
  return .failed none

def mkNormSimpScriptStep (ctx : NormSimpContext)
    (inGoal : MVarId) (outGoal? : Option GoalWithMVars)
    (usedTheorems : Simp.UsedSimps) :
    MetaM UnstructuredScriptStep := do
  let tactic ←
    mkNormSimpOnlySyntax inGoal ctx.useHyps ctx.configStx? usedTheorems
  return {
    tacticSeq := #[tactic]
    otherSolvedGoals := #[]
    outGoals := outGoal?.toArray
    inGoal
  }

def SimpResult.toNormRuleResult (ruleName : DisplayRuleName)
    (ctx : NormSimpContext) (originalGoal : MVarId)
    (originalGoalMVars : HashSet MVarId) (generateScript : Bool) :
    SimpResult → MetaM NormRuleResult
  | .unchanged newGoal => do
    let scriptStep? :=
      if generateScript then
        some $ .dummy originalGoal ⟨newGoal, originalGoalMVars⟩
      else
        none
    return .failed scriptStep?
  | .solved usedTheorems => do
    let scriptStep? ← mkScriptStep? none usedTheorems
    return .proved scriptStep?
  | .simplified newGoal usedTheorems => do
    let scriptStep? ← mkScriptStep? (some newGoal) usedTheorems
    return .succeeded newGoal none scriptStep?
  where
    @[inline, always_inline]
    mkScriptStep? (newGoal? : Option MVarId) (usedTheorems : Simp.UsedSimps) :
        MetaM (Except DisplayRuleName UnstructuredScriptStep) := do
      if generateScript then
        let newGoal? := newGoal?.map λ g => ⟨g, originalGoalMVars⟩
        .ok <$> mkNormSimpScriptStep ctx originalGoal newGoal? usedTheorems
      else
        return .error ruleName

def normSimpCore (ctx : NormSimpContext)
    (localSimpRules : Array LocalNormSimpRule) (goal : MVarId)
    (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  goal.withContext do
    aesop_trace[stepsNormalization] "Running normalisation simp."
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

    -- It can happen that simp 'solves' the goal but leaves some mvars
    -- unassigned. In this case, we treat the goal as unchanged.
    let result ←
      match result with
      | .solved .. =>
        let anyMVarDropped ← goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)
        if anyMVarDropped then
            aesop_trace[stepsNormalization] "Normalisation simp solved the goal but dropped some metavariables. Skipping normalisation simp."
            restoreState preState
            pure $ .unchanged goal
        else
            aesop_trace[stepsNormalization] "simp proved the goal."
            pure result
      | .simplified newGoal .. =>
        aesop_trace[stepsNormalization] "New goal:{indentD newGoal}"
        pure result
      | .unchanged .. =>
        aesop_trace[stepsNormalization] "simp left the goal unchanged."
        pure result

    result.toNormRuleResult .normSimp ctx goal goalMVars generateScript

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
      normSimpCore ctx localSimpRules goal goalMVars generateScript
    catch e =>
      throwError "aesop: error in norm simp: {e.toMessageData}"

def normSimp (ctx : NormSimpContext) (localSimpRules : Array LocalNormSimpRule)
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    ProfileT MetaM NormRuleResult := do
  if ! ctx.enabled then
    aesop_trace[stepsNormalization] "Skipping norm simp since it is disabled."
    return .failed none
  profiling
    (checkedNormSimpCore ctx localSimpRules goal goalMVars generateScript)
    λ _ elapsed => recordAndTraceRuleProfile
      { rule := .normSimp, elapsed, successful := true }

def normUnfoldCore (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  aesop_trace[stepsNormalization] "Running normalisation unfold."
  let (result, scriptBuilder?) ←
    unfoldManyStarWithScript goal (unfoldRules.find? ·) generateScript
  match result with
  | .unchanged =>
    aesop_trace[stepsNormalization] "No definitions unfolded."
    return .failed none
  | .changed newGoal _ =>
    aesop_trace[stepsNormalization] "New goal:{indentD newGoal}"
    let scriptStep? ← do
      match scriptBuilder? with
      | some unfoldScriptBuilder =>
        pure $ .ok {
          tacticSeq := ← unfoldScriptBuilder.unstructured.run
          inGoal := goal
          outGoals := #[⟨newGoal, goalMVars⟩]
          otherSolvedGoals := {}
        }
      | none => pure $ .error .normUnfold
    return .succeeded newGoal none scriptStep?

def checkedNormUnfoldCore (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    MetaM NormRuleResult := do
  checkSimp "unfold simp" (mayCloseGoal := false) goal do
    try
      normUnfoldCore unfoldRules goal goalMVars generateScript
    catch e =>
      throwError "aesop: error in norm unfold: {e.toMessageData}"

def normUnfold (unfoldRules : PHashMap Name (Option Name))
    (goal : MVarId) (goalMVars : HashSet MVarId) (generateScript : Bool) :
    ProfileT MetaM NormRuleResult :=
  profiling (checkedNormUnfoldCore unfoldRules goal goalMVars generateScript)
    λ _ elapsed => recordAndTraceRuleProfile
      { rule := .normUnfold, elapsed, successful := true }

inductive NormSeqResult where
  | proved (script? : Except DisplayRuleName UnstructuredScript)
  | unproved (goal : MVarId) (branchState : BranchState)
      (script? : Except DisplayRuleName UnstructuredScript)

abbrev NormStep :=
  MVarId → BranchState → Array (IndexMatchResult NormRule) →
  Array (IndexMatchResult NormRule) → ProfileT MetaM NormRuleResult

def runNormSteps (rs : RuleSet) (goal : MVarId) (bs : BranchState)
    (maxIterations : Nat) (steps : Array NormStep) (stepsNe : 0 < steps.size) :
    ProfileT MetaM NormSeqResult := do
  let mut iteration := 0
  let mut step : Fin steps.size := ⟨0, stepsNe⟩
  let mut goal := goal
  let mut bs := bs
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
    match ← steps[step] goal bs preSimpRules postSimpRules with
    | .succeeded newGoal branchState? scriptStep? =>
      goal := newGoal
      script? := return (← script?).push (← scriptStep?)
      bs := branchState?.getD bs
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
        return .unproved goal bs script?
  throwError "aesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."

def NormStep.runPreSimpRules (options : Options')
    (mvars : UnorderedArraySet MVarId) : NormStep :=
  λ goal bs preSimpRules _ =>
    runFirstNormRule goal mvars bs options preSimpRules

def NormStep.runPostSimpRules (options : Options')
    (mvars : UnorderedArraySet MVarId) : NormStep :=
  λ goal bs _ postSimpRules =>
    runFirstNormRule goal mvars bs options postSimpRules

def NormStep.unfold (rs : RuleSet) (options : Options')
    (mvars : HashSet MVarId) : NormStep :=
  λ goal _ _ _ =>
    normUnfold rs.unfoldRules goal mvars options.generateScript

def NormStep.simp (rs : RuleSet) (ctx : NormSimpContext) (options : Options')
    (mvars : HashSet MVarId) : NormStep :=
  λ goal _ _ _ =>
    normSimp ctx rs.localNormSimpLemmas goal mvars options.generateScript

partial def normalizeGoalMVar (rs : RuleSet) (normSimpContext : NormSimpContext)
    (options : Options') (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (bs : BranchState) :
    ProfileT MetaM NormSeqResult := do
  aesop_trace[steps] "Goal before normalisation:{indentD goal}"
  let mvarsHashSet := .ofArray mvars.toArray
  let mut normSteps := #[
    NormStep.runPreSimpRules options mvars,
    NormStep.unfold rs options mvarsHashSet,
    NormStep.simp rs normSimpContext options mvarsHashSet,
    NormStep.runPostSimpRules options mvars
  ]
  runNormSteps rs goal bs options.maxNormIterations normSteps (by simp)

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) : SearchM Q Bool := do
  let g ← gref.get
  match g.normalizationState with
  | .provenByNormalization .. => return true
  | .normal .. => return false
  | .notNormal => pure ()
  aesop_trace[steps] "Normalising the goal"
  let ctx ← read
  let profilingEnabled ← isProfilingEnabled
  let profile ← getThe Profile
  let ((normResult, profile), postState) ←
    (← gref.get).runMetaMInParentState do
      normalizeGoalMVar ctx.ruleSet ctx.normSimpContext ctx.options
        g.preNormGoal g.mvars g.branchState
      |>.run profilingEnabled profile
  modify λ s => { s with profile }
  match normResult with
  | .unproved postGoal postBranchState script? =>
    gref.modify λ g =>
      g.setNormalizationState (.normal postGoal postState script?)
      |>.setBranchState postBranchState
    return false
  | .proved script? =>
    gref.modify λ g =>
      g.setNormalizationState (.provenByNormalization postState script?)
    gref.markProvenByNormalization
    return true

end Aesop
