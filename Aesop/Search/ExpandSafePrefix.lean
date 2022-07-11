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
  private partial def expandFirstSafePrefixGoal (gref : GoalRef) :
      SearchM Q Unit :=
    withIncRecDepth do
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
        aesop_trace[steps] do
          if safeRapps.size > 1 then
            let rappIds ← safeRapps.mapM λ rref => return (← rref.get).id
            aesop_trace![steps] "Goal has multiple safe rapps ({rappIds}). Expanding only the first one."
        expandFirstSafePrefixRapp safeRapps[0]

  private partial def expandFirstSafePrefixRapp (rref : RappRef) :
      SearchM Q Unit := do
    (← rref.get).children.forM expandFirstSafePrefixMVarCluster

  private partial def expandFirstSafePrefixMVarCluster (cref : MVarClusterRef) :
      SearchM Q Unit := do
    (← cref.get).goals.forM expandFirstSafePrefixGoal
end

def expandFirstSafePrefix : SearchM Q Unit := do
  aesop_trace[steps] "Expanding safe subtree of the root goal."
  expandFirstSafePrefixGoal (← getRootGoal)

end Aesop
