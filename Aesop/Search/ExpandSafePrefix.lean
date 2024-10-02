/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Exception
import Aesop.Search.Expansion

open Lean Lean.Meta

namespace Aesop

declare_aesop_exception
  safeExpansionFailedException safeExpansionFailedExceptionId
  isSafeExpansionFailedException

structure SafeExpansionM.State where
  numRapps : Nat := 0

abbrev SafeExpansionM Q [Queue Q] := StateRefT SafeExpansionM.State (SearchM Q)

variable [Queue Q]

private def Goal.isSafeExpanded (g : Goal) : BaseIO Bool :=
  (pure g.unsafeRulesSelected) <||> g.hasSafeRapp

-- Typeclass inference struggles with inferring Q, so we have to lift
-- explicitly.
private def liftSearchM (x : SearchM Q α) : SafeExpansionM Q α :=
  x

mutual
  private partial def expandSafePrefixGoal (gref : GoalRef) :
      SafeExpansionM Q Unit := do
    let g ← gref.get
    if g.state.isProven then
      aesop_trace[steps] "Skipping safe rule expansion of goal {g.id} since it is already proven."
      return
    if ! (← g.isSafeExpanded) then
      aesop_trace[steps] "Applying safe rules to goal {g.id}."
      if ← liftSearchM $ normalizeGoalIfNecessary gref then
          -- Goal was already proved by normalisation.
          return
      let maxRapps := (← read).options.maxSafePrefixRuleApplications
      if maxRapps > 0 && (← getThe SafeExpansionM.State).numRapps > maxRapps then
        throw safeExpansionFailedException
      discard $ liftSearchM $ runFirstSafeRule gref
      modifyThe SafeExpansionM.State λ s =>
        { s with numRapps := s.numRapps + 1 }
    else
      aesop_trace[steps] "Skipping safe rule expansion of goal {g.id} since safe rules have already been applied."
    let g ← gref.get
    if g.state.isProven then
      return
    let safeRapps ← g.safeRapps
    if h₁ : 0 < safeRapps.size then
      if safeRapps.size > 1 then
        throwError "aesop: internal error: goal {g.id} has multiple safe rapps"
      expandFirstPrefixRapp safeRapps[0]

  private partial def expandFirstPrefixRapp (rref : RappRef) :
      SafeExpansionM Q Unit := do
    (← rref.get).children.forM expandSafePrefixMVarCluster

  private partial def expandSafePrefixMVarCluster (cref : MVarClusterRef) :
      SafeExpansionM Q Unit := do
    (← cref.get).goals.forM expandSafePrefixGoal
end

def expandSafePrefix : SearchM Q Bool := do
  aesop_trace[steps] "Expanding safe subtree of the root goal."
  try
    expandSafePrefixGoal (← getRootGoal) |>.run' {}
    return true
  catch e =>
    if isSafeExpansionFailedException e then
      return false
    else
      throw e

end Aesop
