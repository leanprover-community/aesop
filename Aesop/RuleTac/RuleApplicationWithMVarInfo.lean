/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean Lean.Meta

namespace Aesop

/-
A `RuleApplication` reports the `postState` and the generated goals as an `Array
MVarId`. A `RuleApplicationWithMVarInfo` also contains the `postState`, but
contains additional information on how the tactic which generated the rule
application manipulated metavariables.

Let `ms` be the metavariables which were declared but not assigned by the
tactic.

- `goals` are those `ms` which do not occur in any other `m ∈ ms`. Each of these
  goals `g` is associated with the set of metavariables which occur in `g`.
- `mvars` are the metavariables which occur in the `goals`.
- `introducedMVars` are those `ms` which are not goals (i.e. the `mvars` which
  were not declared before the tactic was run).
- `assignedMVars` contains metavariables assigned by the tactic. These are
  metavariables that were previously declared and unassigned and are now
  assigned.
-/
structure RuleApplicationWithMVarInfo where
  postState : Meta.SavedState
  goals : Array (MVarId × UnorderedArraySet MVarId)
  mvars : UnorderedArraySet MVarId
  introducedMVars : UnorderedArraySet MVarId
  assignedMVars : UnorderedArraySet MVarId

namespace RuleApplicationWithMVarInfo

protected def check (preState : Meta.SavedState) (parentGoal : MVarId)
    (r : RuleApplicationWithMVarInfo) : MetaM (Option MessageData) := do
  -- Check introduced mvars
  let actualIntroducedMVars ← introducedExprMVars preState r.postState
  let reportedIntroducedMVars := r.goals.map (·.fst) ++ r.introducedMVars.toArray
  let unreportedIntroducedMVars :=
    actualIntroducedMVars.filter (! reportedIntroducedMVars.contains ·)
  unless unreportedIntroducedMVars.isEmpty do
    return m!"the following mvars were introduced but do not appear in the goals: {unreportedIntroducedMVars.map (·.name)}"
  let overreportedIntroducedMVars :=
    r.introducedMVars.toArray.filter (! actualIntroducedMVars.contains ·)
  unless overreportedIntroducedMVars.isEmpty do
    return m!"the following mvars were reported as introduced but were already present before the rule was applied: {overreportedIntroducedMVars.map (·.name)}"

  -- Check assigned mvars
  let actualAssignedMVars :=
    (← assignedExprMVars preState r.postState).erase parentGoal
  unless actualAssignedMVars.equalSet r.assignedMVars.toArray do
    return m!"rule reported wrong assigned mvars.\n  reported: {r.assignedMVars.toArray.map (·.name)}\n  actual: {actualAssignedMVars.map (·.name)}"
  return none

end RuleApplicationWithMVarInfo

def RuleApplication.toRuleApplicationWithMVarInfo
    (parentMVars : UnorderedArraySet MVarId) (r : RuleApplication) :
    MetaM RuleApplicationWithMVarInfo :=
  r.postState.runMetaM' do
    -- Get assigned mvars
    r.postState.runMetaM' do
    let assignedMVars ← parentMVars.filterM λ mvarId =>
        isExprMVarAssigned mvarId <||> isMVarDelayedAssigned mvarId

    -- Get goals and mvars
    let mut goalsAndMVars := #[]
    let mut mvars := {}
    for g in r.goals do
      let gMVars ← .ofHashSet <$> getUnassignedGoalMVarDependencies g
      mvars := mvars.merge gMVars
      goalsAndMVars := goalsAndMVars.push (g, gMVars)
    let goals :=
      if mvars.isEmpty then
        goalsAndMVars
      else
        goalsAndMVars.filter λ (g, _) => ! mvars.contains g

    -- Get introduced mvars
    let introducedMVars := mvars.filter (! parentMVars.contains ·)

    return {
      postState := r.postState
      goals, mvars, introducedMVars, assignedMVars
    }

end Aesop
