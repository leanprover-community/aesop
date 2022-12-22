/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Expansion

open Lean Lean.Meta

namespace Aesop

variable [Queue Q]

private def Goal.isSafeExpanded (g : Goal) : BaseIO Bool :=
  (pure g.unsafeRulesSelected) <||> g.hasSafeRapp

mutual
  private partial def expandSafePrefixGoal (gref : GoalRef) :
      SearchM Q Unit :=
    -- TODO this may or may not be necessary to prevent a stack overflow when
    -- the safe rule set loops.
    withIncRecDepth do withIncRecDepth do
      let g ← gref.get
      if g.state.isProven then
        aesop_trace[steps] "Skipping safe rule expansion of goal {g.id} since it is already proven."
        return
      if ! (← g.isSafeExpanded) then
        aesop_trace[steps] "Applying safe rules to goal {g.id}."
        if ← normalizeGoalIfNecessary gref then
            -- Goal was already proved by normalisation.
            return
        discard $ runFirstSafeRule gref
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
      SearchM Q Unit := do
    (← rref.get).children.forM expandSafePrefixMVarCluster

  private partial def expandSafePrefixMVarCluster (cref : MVarClusterRef) :
      SearchM Q Unit := do
    (← cref.get).goals.forM expandSafePrefixGoal
end

def expandSafePrefix : SearchM Q Unit := do
  aesop_trace[steps] "Expanding safe subtree of the root goal."
  expandSafePrefixGoal (← getRootGoal)

end Aesop
