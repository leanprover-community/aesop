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
import Aesop.Tree
import Aesop.Util

open Lean
open Lean.Meta
open Lean.Elab.Tactic (liftMetaTacticAux TacticM)

namespace Aesop

variable [Aesop.Queue Q]

partial def nextActiveGoal : SearchM Q GoalRef := do
  let some gref ← popGoal?
    | throwError "aesop/expandNextGoal: internal error: no active goals left"
  if ! (← (← gref.get).isActive) then
    aesop_trace[steps] "Skipping inactive goal {(← gref.get).id}."
    nextActiveGoal
  else
    return gref

def expandNextGoal : SearchM Q Unit := do
  let gref ← nextActiveGoal
  aesop_trace[steps] "Expanding {← (← gref.get).toMessageData (← TraceModifiers.get)}"
  let maxRappDepth := (← read).options.maxRuleApplicationDepth
  if maxRappDepth != 0 && (← gref.get).depth >= maxRappDepth then
    aesop_trace[steps] "Skipping goal since it is beyond the maximum rule application depth ({maxRappDepth})."
    gref.markForcedUnprovable
    return
  expandGoal gref
  let currentIteration ← getIteration
  gref.modify λ g => g.setLastExpandedInIteration currentIteration
  if ← (← gref.get).isActive then
    enqueueGoals #[gref]

def checkGoalLimit : SearchM Q Unit := do
  let maxGoals := (← read).options.maxGoals
  let currentGoals := (← getTree).numGoals
  if maxGoals != 0 && currentGoals >= maxGoals then throwError
    "aesop: maximum number of goals ({maxGoals}) reached. Set the 'maxGoals' option to increase the limit."

def checkRappLimit : SearchM Q Unit := do
  let maxRapps := (← read).options.maxRuleApplications
  let currentRapps := (← getTree).numRapps
  if maxRapps != 0 && currentRapps >= maxRapps then throwError
    "aesop: maximum number of rule applications ({maxRapps}) reached. Set the 'maxRuleApplications' option to increase the limit."

def finishIfProven : SearchM Q Bool := do
  let root ← getRootMVarCluster
  unless (← root.get).state.isProven do
    return false
  aesop_trace[steps] "Root node is proven. Linking proofs."
  let rootGoal := (← read).rootGoalMVar
  withMVarContext rootGoal do
    extractProof
    let (some proof) ← getExprMVarAssignment? rootGoal | throwError
      "aesop: internal error: root goal mvar is not assigned"
    let proof ← instantiateMVars proof
    if proof.hasExprMVar then throwError
      m!"aesop: internal error: extracted proof has metavariables." ++ MessageData.node #[
        m!"Proof: {proof}",
        m!"Unassigned metavariables: {(← getMVarsNoDelayed proof).map (·.name)}"
      ]
    assignExprMVar rootGoal proof
    aesop_trace[proof] "Final proof:{indentExpr proof}"
    return true

partial def searchLoop : SearchM Q Unit := do
  aesop_trace[steps] "=== Search loop iteration {← getIteration}"
  let root := (← getTree).root
  if (← root.get).state.isUnprovable then
    throwError "aesop: failed to prove the goal after exhaustive search"
  if ← finishIfProven then
    return
  checkGoalLimit
  checkRappLimit
  expandNextGoal
  aesop_trace[stepsTree] "Current search tree:{indentD $ ← (← (← getRootGoal).get).treeToMessageData (← TraceModifiers.get)}"
  aesop_trace[stepsActiveGoalQueue] "Current active goals:{← formatQueue}"
  checkInvariantsIfEnabled
  incrementIteration
  searchLoop

def search (Q) [Queue Q] (goal : MVarId) (ruleSet? : Option RuleSet := none)
     (options : Aesop.Options := {}) (profile : Profile := {}) :
     MetaM Profile := do
  checkNotAssigned goal `aesop
  let go : SearchM Q Unit := try searchLoop finally freeTree
  let ruleSet ← do
    match ruleSet? with
    | none => Frontend.getDefaultAttributeRuleSet
    | some ruleSet => pure ruleSet
  let (_, state, _) ← SearchM.run ruleSet options goal profile go
  return state.profile

def bestFirst (goal : MVarId) (ruleSet? : Option RuleSet := none)
    (options : Aesop.Options := {}) (profile : Profile := {}) : MetaM Profile :=
  search BestFirstQueue goal ruleSet? options profile

end Aesop
