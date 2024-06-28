/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.RuleTac
import Aesop.RuleTac.ElabRuleTerm
import Aesop.Script.SpecificTactics
import Aesop.Search.Expansion.Basic
import Aesop.Search.Expansion.Simp
import Aesop.Search.RuleSelection
import Aesop.Search.SearchM

open Lean Lean.Meta Aesop.Script

namespace Aesop

namespace NormM

structure Context where
  options : Options'
  ruleSet : LocalRuleSet
  normSimpContext : NormSimpContext
  statsRef : StatsRef

end NormM

abbrev NormM := ReaderT NormM.Context MetaM

instance : MonadBacktrack Meta.SavedState NormM where
  saveState := Meta.saveState
  restoreState s := s.restore

instance : MonadStats NormM where
  readStatsRef := return (← read).statsRef

instance [Queue Q] : MonadLift NormM (SearchM Q) where
  monadLift x := do x.run { (← read) with }

inductive NormRuleResult
  | succeeded (goal : MVarId) (steps? : Option (Array Script.LazyStep))
  | proved (steps? : Option (Array Script.LazyStep))

namespace NormRuleResult

def newGoal? : NormRuleResult → Option MVarId
  | succeeded goal .. => goal
  | proved .. => none

def steps? : NormRuleResult → Option (Array Script.LazyStep)
  | .succeeded (steps? := steps?) .. | .proved (steps? := steps?) .. => steps?

end NormRuleResult

def optNormRuleResultEmoji : Option NormRuleResult → String
  | some (.succeeded ..) => ruleSuccessEmoji
  | some (.proved ..) => ruleProvedEmoji
  | none => ruleFailureEmoji

@[inline, always_inline]
def withNormTraceNode (ruleName : DisplayRuleName)
    (k : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) :=
  withAesopTraceNode .steps fmt do
    let result? ← k
    if let some newGoal := result?.bind (·.newGoal?) then
      aesop_trace[steps] newGoal
    return result?
  where
    fmt (r : Except Exception (Option NormRuleResult)) : NormM MessageData := do
      let emoji := exceptRuleResultToEmoji (optNormRuleResultEmoji ·) r
      return m!"{emoji} {ruleName}"

def runNormRuleTac (rule : NormRule) (input : RuleTacInput) :
    MetaM (Option NormRuleResult) := do
  let preMetaState ← saveState
  let result? ← runRuleTac rule.tac.run rule.name preMetaState input
  match result? with
  | Sum.inl e =>
    aesop_trace[steps] e.toMessageData
    return none
  | Sum.inr result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    restoreState rapp.postState
    if rapp.goals.isEmpty then
      return some $ .proved rapp.scriptSteps?
    let (#[g]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    let mvars := .ofArray input.mvars.toArray
    if ← Check.rules.isEnabled then
      let actualMVars ← rapp.postState.runMetaM' g.getMVarDependencies
      if ! actualMVars == mvars then
         err "the goal produced by the rule depends on different metavariables than the original goal."
    return some $ .succeeded g rapp.scriptSteps?
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

def runNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rule : IndexMatchResult NormRule) : NormM (Option NormRuleResult) := do
  profilingRule (.ruleName rule.rule.name) (λ result => result.isSome) do
    let ruleInput := {
      indexMatchLocations := rule.locations
      patternInstantiations := rule.patternInstantiations
      options := (← read).options
      goal, mvars
    }
    withNormTraceNode (.ruleName rule.rule.name) do
      runNormRuleTac rule.rule ruleInput

def runFirstNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rules : Array (IndexMatchResult NormRule)) :
    NormM (Option (DisplayRuleName × NormRuleResult)) := do
  for rule in rules do
    let result? ← runNormRule goal mvars rule
    if let some result := result? then
      return some (rule.rule.name, result)
  return none

def mkNormSimpScriptStep
    (preGoal : MVarId) (postGoal? : Option MVarId)
    (preState postState : Meta.SavedState) (usedTheorems : Simp.UsedSimps) :
    NormM Script.LazyStep := do
  let ctx := (← read).normSimpContext
  let tacticBuilder :=
    TacticBuilder.simpAllOrSimpAtStarOnly (simpAll := ctx.useHyps) preGoal
      ctx.configStx? usedTheorems
  return {
    postGoals := postGoal?.toArray
    tacticBuilders := #[tacticBuilder]
    preGoal, preState, postState
  }

def SimpResult.toNormRuleResult (originalGoal : MVarId)
    (preState postState : Meta.SavedState) :
    SimpResult → NormM (Option NormRuleResult)
  | .unchanged => return none
  | .solved usedTheorems => do
    let step ←
      mkNormSimpScriptStep originalGoal none preState postState usedTheorems
    return some $ .proved #[step]
  | .simplified newGoal usedTheorems => do
    let step ←
      mkNormSimpScriptStep originalGoal newGoal preState postState usedTheorems
    return some $ .succeeded newGoal #[step]

def normSimpCore (goal : MVarId) (goalMVars : HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  let ctx := (← read).normSimpContext
  goal.withContext do
    let preState ← saveState
    let localRules := (← read).ruleSet.localNormSimpRules
    let result ←
      if ctx.useHyps then
        let (ctx, simprocs) ←
          addLocalRules localRules ctx.toContext ctx.simprocs
            (isSimpAll := true)
        Aesop.simpAll goal ctx simprocs
      else
        let (ctx, simprocs) ←
          addLocalRules localRules ctx.toContext ctx.simprocs
            (isSimpAll := false)
        Aesop.simpGoalWithAllHypotheses goal ctx simprocs

    -- It can happen that simp 'solves' the goal but leaves some mvars
    -- unassigned. In this case, we treat the goal as unchanged.
    let result ←
      match result with
      | .solved .. =>
        let anyMVarDropped ← goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)
        if anyMVarDropped then
          aesop_trace[steps] "Normalisation simp solved the goal but dropped some metavariables. Skipping normalisation simp."
          restoreState preState
          pure .unchanged
        else
          pure result
      | .unchanged .. =>
        aesop_trace[steps] "norm simp left the goal unchanged"
        pure result
      | .simplified .. =>
        pure result

    let postState ← saveState
    result.toNormRuleResult goal preState postState
where
  addLocalRules (localRules : Array LocalNormSimpRule) (ctx : Simp.Context)
      (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
      NormM (Simp.Context × Simp.SimprocsArray) :=
    localRules.foldlM (init := (ctx, simprocs)) λ (ctx, simprocs) r =>
      try
        elabRuleTermForSimpMetaM goal r.simpTheorem ctx simprocs isSimpAll
      catch _ =>
        return (ctx, simprocs)

@[inline, always_inline]
def checkSimp (name : String) (mayCloseGoal : Bool) (goal : MVarId)
    (x : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) := do
  if ! (← Check.rules.isEnabled) then
    x
  else
    let preMetaState ← saveState
    let result? ← x
    let newGoal? := result?.bind (·.newGoal?)
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
    return result?

def normSimp (goal : MVarId) (goalMVars : HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  profilingRule .normSimp (wasSuccessful := λ _ => true) do
    checkSimp "norm simp" (mayCloseGoal := true) goal do
      try
        withNormTraceNode .normSimp do
          withMaxHeartbeats (← read).options.maxSimpHeartbeats do
            normSimpCore goal goalMVars
      catch e =>
        throwError "aesop: error in norm simp: {e.toMessageData}"

def normUnfoldCore (goal : MVarId) : NormM (Option NormRuleResult) := do
  let unfoldRules := (← read).ruleSet.unfoldRules
  let (result, steps) ← unfoldManyStarS goal (unfoldRules.find? ·) |>.run
  match result with
  | .unchanged =>
    aesop_trace[steps] "nothing to unfold"
    return none
  | .changed newGoal _ =>
    return some $ .succeeded newGoal steps

def normUnfold (goal : MVarId) : NormM (Option NormRuleResult) := do
  profilingRule .normUnfold (wasSuccessful := λ _ => true) do
    checkSimp "unfold simp" (mayCloseGoal := false) goal do
      try
        withNormTraceNode .normUnfold do
          withMaxHeartbeats (← read).options.maxUnfoldHeartbeats do
            normUnfoldCore goal
      catch e =>
        throwError "aesop: error in norm unfold: {e.toMessageData}"

inductive NormSeqResult where
  | proved (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | changed (goal : MVarId)
      (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | unchanged

def NormRuleResult.toNormSeqResult (ruleName : DisplayRuleName) :
    NormRuleResult → NormSeqResult
  | .proved steps? => .proved #[(ruleName, steps?)]
  | .succeeded goal steps? => .changed goal #[(ruleName, steps?)]

def optNormRuleResultToNormSeqResult :
    Option (DisplayRuleName × NormRuleResult) → NormSeqResult
  | some (ruleName, r) => r.toNormSeqResult ruleName
  | none => .unchanged

abbrev NormStep :=
  MVarId → Array (IndexMatchResult NormRule) →
  Array (IndexMatchResult NormRule) → NormM NormSeqResult

def runNormSteps (goal : MVarId) (steps : Array NormStep)
    (stepsNe : 0 < steps.size) : NormM NormSeqResult := do
  let ctx ← readThe NormM.Context
  let maxIterations := ctx.options.maxNormIterations
  let mut iteration := 0
  let mut step : Fin steps.size := ⟨0, stepsNe⟩
  let mut goal := goal
  let mut scriptSteps := #[]
  let mut preSimpRules := ∅
  let mut postSimpRules := ∅
  let mut anySuccess := false
  while iteration < maxIterations do
    if step.val == 0 then
      let rules ← selectNormRules ctx.ruleSet goal
      let (preSimpRules', postSimpRules') :=
        rules.partition λ r => r.rule.extra.penalty < (0 : Int)
      preSimpRules := preSimpRules'
      postSimpRules := postSimpRules'
    match ← steps[step] goal preSimpRules postSimpRules with
    | .changed newGoal scriptSteps' =>
      anySuccess := true
      goal := newGoal
      scriptSteps := scriptSteps ++ scriptSteps'
      iteration := iteration + 1
      step := ⟨0, stepsNe⟩
    | .proved scriptSteps' =>
      scriptSteps := scriptSteps ++ scriptSteps'
      return .proved scriptSteps
    | .unchanged =>
      if h : step.val + 1 < steps.size then
        step := ⟨step.val + 1, h⟩
      else
        if anySuccess then
          return .changed goal scriptSteps
        else
          return .unchanged
  throwError "aesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."

def NormStep.runPreSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, preSimpRules, _ => do
    optNormRuleResultToNormSeqResult <$> runFirstNormRule goal mvars preSimpRules

def NormStep.runPostSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, _, postSimpRules =>
    optNormRuleResultToNormSeqResult <$> runFirstNormRule goal mvars postSimpRules

def NormStep.unfold : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).options.enableUnfold then
      aesop_trace[steps] "norm unfold is disabled (options := \{ ..., enableUnfold := false })"
      return .unchanged
    let r := (← normUnfold goal).map (.normUnfold, ·)
    return optNormRuleResultToNormSeqResult r

def NormStep.simp (mvars : HashSet MVarId) : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).normSimpContext.enabled then
      aesop_trace[steps] "norm simp is disabled (simp_options := \{ ..., enabled := false })"
      return .unchanged
    let r := (← normSimp goal mvars).map (.normSimp, ·)
    return optNormRuleResultToNormSeqResult r

partial def normalizeGoalMVar (goal : MVarId)
    (mvars : UnorderedArraySet MVarId) : NormM NormSeqResult := do
  let mvarsHashSet := .ofArray mvars.toArray
  let mut normSteps := #[
    NormStep.runPreSimpRules mvars,
    NormStep.unfold,
    NormStep.simp mvarsHashSet,
    NormStep.runPostSimpRules mvars
  ]
  runNormSteps goal normSteps
    (by simp (config := { decide := true }) [normSteps])

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) [Aesop.Queue Q] :
    SearchM Q Bool := do
  let g ← gref.get
  let preGoal := g.preNormGoal
  if ← g.isRoot then
    -- For the root goal, we skip normalization.
    let rootState ← getRootMetaState
    gref.modify λ g => g.setNormalizationState (.normal preGoal rootState #[])
    return false
  match g.normalizationState with
  | .provenByNormalization .. => return true
  | .normal .. => return false
  | .notNormal => pure ()
  let (normResult, postState) ← controlAt MetaM λ runInBase => do
    (← gref.get).runMetaMInParentState do
      runInBase $ normalizeGoalMVar preGoal g.mvars
  match normResult with
  | .changed postGoal script? =>
    gref.modify (·.setNormalizationState (.normal postGoal postState script?))
    return false
  | .unchanged =>
    gref.modify (·.setNormalizationState (.normal preGoal postState #[]))
    return false
  | .proved script? =>
    gref.modify
      (·.setNormalizationState (.provenByNormalization postState script?))
    gref.markProvenByNormalization
    return true

end Aesop
