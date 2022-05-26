/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tree.Data

open Lean
open Lean.Meta

namespace Aesop

structure SafePrefixGoal where
  metaState : Meta.SavedState
  goal : MVarId
  state : GoalState

def SafePrefixGoal.toMessageData (g : SafePrefixGoal) : MetaM MessageData :=
  g.metaState.runMetaM' do
    addMessageContextFull $ m!"({g.state})\n{g.goal}"


def SafePrefix := Array SafePrefixGoal

def SafePrefix.toMessageData (p : SafePrefix) : MetaM MessageData :=
  return MessageData.joinSepArray (← p.mapM (·.toMessageData)) "\n\n"

def SafePrefixes := Array SafePrefix

def SafePrefixes.toMessageData (ps : SafePrefixes) : MetaM MessageData :=
  return MessageData.joinSepArray (← ps.mapM (·.toMessageData)) "\n\n==========\n\n"

private def Goal.safeRapps (g : Goal) : MetaM (Array RappRef) :=
  g.children.filterM λ rref =>
    return (← rref.get).appliedRule.isSafe

private def Goal.toSafePrefixGoal (g : Goal) : MetaM SafePrefixGoal := do
  let (goal, metaState) ← g.currentGoalAndMetaState
  return { goal, metaState, state := g.state }

mutual
  private partial def extractSafePrefixesGoal (g : Goal)
      (acc : SafePrefixes) : MetaM SafePrefixes := do
    let safeRapps ← g.safeRapps
    if safeRapps.isEmpty then
      let prefixGoal ← g.toSafePrefixGoal
      if acc.isEmpty then
        return #[#[prefixGoal]]
      else
        return acc.map (·.push $ ← g.toSafePrefixGoal)
    else
      safeRapps.concatMapM λ rref => do
        extractSafePrefixesRapp (← rref.get) acc

  private partial def extractSafePrefixesRapp (r : Rapp) (acc : SafePrefixes) :
      MetaM SafePrefixes :=
    r.children.foldlM (init := acc) λ acc cref => do
      extractSafePrefixesMVarCluster (← cref.get) acc

  private partial def extractSafePrefixesMVarCluster (c : MVarCluster)
      (acc : SafePrefixes) : MetaM SafePrefixes :=
    c.goals.foldlM (init := acc) λ acc gref => do
      extractSafePrefixesGoal (← gref.get) acc
end

def extractSafePrefixes (gref : GoalRef) : MetaM SafePrefixes := do
  -- let g ← gref.get
  -- let safeRapps ← g.safeRapps
  -- let acc := #[#[← g.toSafePrefixGoal]]
  -- safeRapps.concatMapM λ rref => do
    -- extractSafePrefixesRapp (← rref.get) acc
  extractSafePrefixesGoal (← gref.get) #[]

end Aesop
