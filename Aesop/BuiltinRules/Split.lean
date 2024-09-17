/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop (rule_sets := [builtin]) safe 100]
def splitTarget : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals, steps) ← splitTargetS? input.goal |>.run | throwError
    "nothing to split in target"
  let goals ← goals.mapM (mvarIdToSubgoal input.goal · ∅)
  return (goals, steps, none)

partial def splitHypothesesCore (goal : MVarId) :
    ScriptM (Option (Array MVarId)) :=
  withIncRecDepth do
  let some goals ← splitFirstHypothesisS? goal
    | return none
  let mut subgoals := #[]
  for g in goals do
    if let some subgoals' ← splitHypothesesCore g then
      subgoals := subgoals ++ subgoals'
    else
      subgoals := subgoals.push g
  return subgoals

@[aesop (rule_sets := [builtin]) safe 1000]
def splitHypotheses : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals, steps) ← splitHypothesesCore input.goal |>.run
    | throwError "no splittable hypothesis found"
  let goals ← goals.mapM (mvarIdToSubgoal input.goal · ∅)
  return (goals, steps, none)

end Aesop.BuiltinRules
