/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Options
import Aesop.RuleSet
import Aesop.Script.Check
import Aesop.Script.Main
import Aesop.Search.Expansion
import Aesop.Search.ExpandSafePrefix
import Aesop.Search.Queue
import Aesop.Tree
import Aesop.Frontend.Extension

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
    let msg ←
      if ← wasMaxRuleApplicationDepthReached then
        pure m!"failed to prove the goal. Some goals were not explored because the maximum rule application depth ({(← read).options.maxRuleApplicationDepth}) was reached. Set option 'maxRuleApplicationDepth' to increase the limit."
      else
        pure m!"failed to prove the goal after exhaustive search."
    return msg
  return none

def getProof? : SearchM Q (Option Expr) := do
  getExprMVarAssignment? (← getRootMVarId)

private def withPPAnalyze [Monad m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions (·.setBool `pp.analyze true) x

def finalizeProof : SearchM Q Unit := do
  (← getRootMVarId).withContext do
    extractProof
    let (some proof) ← getProof? | throwError
      "aesop: internal error: root goal is proven but its metavariable is not assigned"
    if (← instantiateMVars proof).hasExprMVar then
      let inner :=
        m!"Proof: {proof}\nUnassigned metavariables: {(← getMVarsNoDelayed proof).map (·.name)}"
      throwError "aesop: internal error: extracted proof has metavariables.{indentD inner}"
    withPPAnalyze do
      aesop_trace[proof] "Final proof:{indentExpr proof}"

def traceScript (completeProof : Bool) : SearchM Q Unit :=
  profiling (λ stats _ elapsed => { stats with script := elapsed }) do
  let options := (← read).options
  if ! options.generateScript then
    return
  let (uscript, proofHasMVars) ←
    if completeProof then extractScript else extractSafePrefixScript
  uscript.checkIfEnabled
  let rootGoal ← getRootMVarId
  let rootState ← getRootMetaState
  aesop_trace[script] "Unstructured script:{indentD $ toMessageData $ ← uscript.renderTacticSeq rootState rootGoal}"
  let sscript? ← uscript.optimize proofHasMVars rootState rootGoal
  checkAndTraceScript uscript sscript? rootState rootGoal options
    (expectCompleteProof := completeProof) "aesop"

def traceTree : SearchM Q Unit := do
  (← (← getRootGoal).get).traceTree .tree

def finishIfProven : SearchM Q Bool := do
  unless (← (← getRootMVarCluster).get).state.isProven do
    return false
  finalizeProof
  traceScript (completeProof := true)
  traceTree
  return true

/--
This function detects whether the search has made progress, meaning that the
remaining goals after safe prefix expansion are different from the initial goal.
We approximate this by checking whether, after safe prefix expansion, either
of the following statements is true.

- There is a safe rapp.
- A subgoal of the preprocessing rule has been modified during normalisation.

This is an approximation because a safe rule could, in principle, leave the
initial goal unchanged.
-/
def treeHasProgress : TreeM Bool := do
  let resultRef ← IO.mkRef false
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      if let some postGoal := g.normalizationState.normalizedGoal? then
        if postGoal != g.preNormGoal then
          resultRef.set true
          return false
      return true)
    (λ rref => do
      let rule := (← rref.get).appliedRule
      if rule.name == preprocessRule.name then
        return true
      else if rule.isUnsafe then
        return false
      else
        resultRef.set true
        return false)
    (λ _ => return true)
    (.mvarCluster (← get).root)
  resultRef.get

def throwAesopEx (mvarId : MVarId) (remainingSafeGoals : Array MVarId)
    (safePrefixExpansionSuccess : Bool) (msg? : Option MessageData) :
    SearchM Q α := do
  if aesop.smallErrorMessages.get (← getOptions) then
    match msg? with
    | none => throwError "tactic 'aesop' failed"
    | some msg => throwError "tactic 'aesop' failed, {msg}"
  else
    let maxRapps := (← read).options.maxSafePrefixRuleApplications
    let suffix :=
      if remainingSafeGoals.isEmpty then
        m!""
      else
        let gs := .joinSep (remainingSafeGoals.toList.map toMessageData) "\n\n"
        let suffix' :=
          if safePrefixExpansionSuccess then
            m!""
          else
            m!"\nThe safe prefix was not fully expanded because the maximum number of rule applications ({maxRapps}) was reached."
        m!"\nRemaining goals after safe rules:{indentD gs}{suffix'}"
    -- Copy-pasta from `Lean.Meta.throwTacticEx`
    match msg? with
    | none => throwError "tactic 'aesop' failed\nInitial goal:{indentD mvarId}{suffix}"
    | some msg => throwError "tactic 'aesop' failed, {msg}\nInitial goal:{indentD mvarId}{suffix}"


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
  let safeExpansionSuccess ← expandSafePrefix
  let safeGoals ← extractSafePrefix
  aesop_trace[proof] do
    match ← getProof? with
    | some proof =>
      (← getRootMVarId).withContext do
        aesop_trace![proof] "{proof}"
    | none => aesop_trace![proof] "<no proof>"
  traceTree
  traceScript (completeProof := false)
  let opts := (← read).options
  if opts.terminal then
    throwAesopEx (← getRootMVarId) safeGoals safeExpansionSuccess err
  if ! (← treeHasProgress) then
    throwAesopEx (← getRootMVarId) #[] safeExpansionSuccess "made no progress"
  if opts.warnOnNonterminal then
    logWarning m!"aesop: {err}"
  if ! safeExpansionSuccess then
    logWarning m!"aesop: safe prefix was not fully expanded because the maximum number of rule applications ({(← read).options.maxSafePrefixRuleApplications}) was reached."
  safeGoals.mapM (clearForwardImplDetailHyps ·)

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

def search (goal : MVarId) (ruleSet? : Option LocalRuleSet := none)
     (options : Aesop.Options := {}) (simpConfig : Simp.Config := {})
     (simpConfigSyntax? : Option Term := none) (stats : Stats := {}) :
     MetaM (Array MVarId × Stats) := do
  goal.checkNotAssigned `aesop
  let options ← options.toOptions'
  let ruleSet ←
    match ruleSet? with
    | none =>
        let rss ← Frontend.getDefaultGlobalRuleSets
        mkLocalRuleSet rss options
    | some ruleSet => pure ruleSet
  let ⟨Q, _⟩ := options.queue
  let (goals, _, _, stats) ←
    SearchM.run ruleSet options simpConfig simpConfigSyntax? goal stats do
      show SearchM Q _ from
      try searchLoop
      finally freeTree
  return (goals, stats)

end Aesop
