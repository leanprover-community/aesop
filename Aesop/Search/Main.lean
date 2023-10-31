/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Frontend.Attribute
import Aesop.Options
import Aesop.RuleSet
import Aesop.Search.Expansion
import Aesop.Search.ExpandSafePrefix
import Aesop.Search.Queue
import Aesop.Tree

open Lean
open Lean.Elab.Tactic (liftMetaTacticAux TacticM)
open Lean.Parser.Tactic (tacticSeq)
open Lean.Meta

namespace Aesop

variable [Aesop.Queue Q]

partial def nextActiveGoal : SearchM Q GoalRef := do
  let some gref ← popGoal?
    | throwError "aesop/expandNextGoal: internal error: no active goals left"
  if ! (← (← gref.get).isActive) then
    nextActiveGoal
  else
    return gref

def expandNextGoal : SearchM Q Unit := do
  let gref ← nextActiveGoal
  let g ← gref.get
  let (initialGoal, initialMetaState) ←
    g.currentGoalAndMetaState (← getRootMetaState)
  let result ← withAesopTraceNode .steps
    (fmt g.id g.priority initialGoal initialMetaState) do
    initialMetaState.runMetaM' do
      aesop_trace[steps] "Initial goal:{indentD initialGoal}"
    let maxRappDepth := (← read).options.maxRuleApplicationDepth
    if maxRappDepth != 0 && (← gref.get).depth >= maxRappDepth then
      aesop_trace[steps] "Treating the goal as unprovable since it is beyond the maximum rule application depth ({maxRappDepth})."
      gref.markForcedUnprovable
      setMaxRuleApplicationDepthReached
      return .failed
    let result ← expandGoal gref
    let currentIteration ← getIteration
    gref.modify λ g => g.setLastExpandedInIteration currentIteration
    if ← (← gref.get).isActive then
      enqueueGoals #[gref]
    return result
  match result with
  | .proved newRapps | .succeeded newRapps => traceNewRapps newRapps
  | .failed => return
  where
    fmt (id : GoalId) (priority : Percent) (initialGoal : MVarId)
        (initialMetaState : Meta.SavedState)
        (result : Except Exception RuleResult) : SearchM Q MessageData := do
      let tgt ← initialMetaState.runMetaM' do
        initialGoal.withContext do
          addMessageContext $ toMessageData (← initialGoal.getType)
      return m!"{exceptRuleResultToEmoji (·.toEmoji) result} (G{id}) [{priority.toHumanString}] ⋯ ⊢ {tgt}"

    traceNewRapps (newRapps : Array RappRef) : SearchM Q Unit := do
      aesop_trace[steps] do
        for rref in newRapps do
          let r ← rref.get
          r.withHeadlineTraceNode .steps
            (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
            withAesopTraceNode .steps (λ _ => return "Metadata") do
              r.traceMetadata .steps
          r.metaState.runMetaM' do
            r.forSubgoalsM λ gref => do
              let g ← gref.get
              g.withHeadlineTraceNode .steps
                (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
                aesop_trace![steps] g.preNormGoal
                withAesopTraceNode .steps (λ _ => return "Metadata") do
                  g.traceMetadata .steps

def checkGoalLimit : SearchM Q (Option MessageData) := do
  let maxGoals := (← read).options.maxGoals
  let currentGoals := (← getTree).numGoals
  if maxGoals != 0 && currentGoals >= maxGoals then
    return m!"maximum number of goals ({maxGoals}) reached. Set the 'maxGoals' option to increase the limit."
  return none

def checkRappLimit : SearchM Q (Option MessageData) := do
  let maxRapps := (← read).options.maxRuleApplications
  let currentRapps := (← getTree).numRapps
  if maxRapps != 0 && currentRapps >= maxRapps then
    return m!"maximum number of rule applications ({maxRapps}) reached. Set the 'maxRuleApplications' option to increase the limit."
  return none

def checkRootUnprovable : SearchM Q (Option MessageData) := do
  let root := (← getTree).root
  if (← root.get).state.isUnprovable then
    let msg :=
      if ← wasMaxRuleApplicationDepthReached then
        m!"failed to prove the goal. Some goals were not explored because the maximum rule application depth ({(← read).options.maxRuleApplicationDepth}) was reached. Set option 'maxRuleApplicationDepth' to increase the limit."
      else
        m!"failed to prove the goal after exhaustive search."
    return msg
  return none

def getProof? : SearchM Q (Option Expr) := do
  let (some proof) ← getExprMVarAssignment? (← getRootMVarId)
    | return none
  instantiateMVars proof

private def withPPAnalyze [Monad m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions (·.setBool `pp.analyze true) x

def finalizeProof : SearchM Q Unit := do
  (← getRootMVarId).withContext do
    extractProof
    let (some proof) ← getProof? | throwError
      "aesop: internal error: root goal is proven but its metavariable is not assigned"
    if proof.hasExprMVar then
      let inner :=
        m!"Proof: {proof}\nUnassigned metavariables: {(← getMVarsNoDelayed proof).map (·.name)}"
      throwError "aesop: internal error: extracted proof has metavariables.{indentD inner}"
    withPPAnalyze do
      aesop_trace[proof] "Final proof:{indentExpr proof}"

open Lean.Elab.Tactic in
def checkRenderedScript (script : Array Syntax.Tactic) : SearchM Q Unit := do
  let initialState ← getRootMetaState
  let rootGoal ← getRootMVarId
  let go : TacticM Unit := do
    setGoals [rootGoal]
    evalTactic $ ← `(tacticSeq| $script:tactic*)
    unless (← getUnsolvedGoals).isEmpty do
      throwError "script executed successfully but did not solve the main goal"
  try
    show MetaM Unit from withoutModifyingState do
      initialState.restore
      go.run { elaborator := .anonymous, recover := false }
        |>.run' { goals := [rootGoal] }
        |>.run'
  catch e => throwError
    "{Check.script.name}: error while executing generated script:{indentD e.toMessageData}"

def checkScriptSteps (script : UnstructuredScript) : SearchM Q Unit := do
  try
    script.validate
  catch e =>
    throwError "{Check.scriptSteps.name}: {e.toMessageData}"

def traceScript : SearchM Q Unit := do
  let options := (← read).options
  if ! options.generateScript then
    return
  try
    let uscript ← (← getRootMVarCluster).extractScript
    if ← Check.scriptSteps.isEnabled then
      checkScriptSteps uscript
    let goal ← getRootMVarId
    let goalMVars ← goal.getMVarDependencies
    let tacticState :=
      { visibleGoals := #[⟨goal, goalMVars⟩], invisibleGoals := {} }
    let script ← uscript.toStructuredScript tacticState
    let script ← script.render tacticState
    if options.traceScript then
      let script ← `(tacticSeq| $script*)
      addTryThisTacticSeqSuggestion (← getRef) script
    if ← Check.script.isEnabled then
      checkRenderedScript script
  catch e =>
    logError m!"aesop: error while generating tactic script:{indentD e.toMessageData}"

def traceTree : SearchM Q Unit := do
  (← (← getRootGoal).get).traceTree .tree

def finishIfProven : SearchM Q Bool := do
  unless (← (← getRootMVarCluster).get).state.isProven do
    return false
  finalizeProof
  traceScript
  traceTree
  return true

-- When we hit a non-fatal error (i.e. the search terminates without a proof
-- because the root goal is unprovable or because we hit a search limit), we
-- usually:
--
-- - Expand all safe rules as much as possible, starting from the root node,
--   until we hit an unsafe rule. We call this the safe prefix.
-- - Extract the proof term for the safe prefix and report the remaining goals.
--
-- The first step is necessary because a goal can become unprovable due to a
-- sibling being unprovable, without the goal ever being expanded. So if we did
-- not expand the safe rules after the fact, the tactic's output would be
-- sensitive to minor changes in, e.g., rule priority.
def handleNonfatalError (err : MessageData) : SearchM Q (Array MVarId) := do
  let opts := (← read).options
  if opts.terminal then
    throwTacticEx `aesop (← getRootMVarId) err
  if opts.warnOnNonterminal then
    logWarning m!"aesop: {err}"
  expandSafePrefix
  let goals ← extractSafePrefix
  aesop_trace[proof] do
    match ← getProof? with
    | some proof =>
      (← getRootMVarId).withContext do
        aesop_trace![proof] "{proof}"
    | none => aesop_trace![proof] "<no proof>"
  traceTree
  return goals

def handleFatalError (e : Exception) : SearchM Q α := do
  traceTree
  throw e

partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "aesop"
    if let (some err) ← checkRootUnprovable then
      handleNonfatalError err
    else if ← finishIfProven then
      return #[]
    else if let (some err) ← checkGoalLimit then
      handleNonfatalError err
    else if let (some err) ← checkRappLimit then
      handleNonfatalError err
    else
      expandNextGoal
      checkInvariantsIfEnabled
      incrementIteration
      searchLoop

def search (goal : MVarId) (ruleSet? : Option RuleSet := none)
     (options : Aesop.Options := {}) (simpConfig : Aesop.SimpConfig := {})
     (simpConfigSyntax? : Option Term := none)
     (profile : Profile := {}) :
     MetaM (Array MVarId × Profile) := do
  goal.checkNotAssigned `aesop
  let options ← options.toOptions'
  let ruleSet ←
    match ruleSet? with
    | none =>
        Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := true)
          options.toOptions
    | some ruleSet => pure ruleSet
  let ⟨Q, _⟩ := options.queue
  let (goals, _, _, profile) ←
    SearchM.run ruleSet options simpConfig simpConfigSyntax? goal profile do
      show SearchM Q _ from
      try searchLoop
      catch e => handleFatalError e
      finally freeTree
  return (goals, profile)

end Aesop
