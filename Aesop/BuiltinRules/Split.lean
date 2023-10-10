/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop (rule_sets [builtin]) safe 100]
def splitTarget : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals) ← splitTarget? input.goal | throwError
    "nothing to split in target"
  let goals := goals.toArray
  let scriptBuilder? :=
    mkScriptBuilder? input.options.generateScript $
      .ofTactic goals.size `(tactic| split)
  return (goals, scriptBuilder?, none)

def splitFirstHypothesis (goal : MVarId) : MetaM (Option (Array MVarId)) :=
  goal.withContext do
    for ldecl in ← getLCtx do
      if let some goals ← splitLocalDecl? goal ldecl.fvarId then
        return goals.toArray
    return none

def splitHypothesesCore (goal : MVarId) : MetaM (Option (Array MVarId)) :=
  saturate1 goal splitFirstHypothesis

elab "aesop_split_hyps" : tactic =>
  Elab.Tactic.liftMetaTactic λ goal => do
    match ← splitHypothesesCore goal with
    | none => throwError "no splittable hypothesis found"
    | some goals => return goals.toList

@[aesop (rule_sets [builtin]) safe 1000]
def splitHypotheses : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals) ← splitHypothesesCore input.goal | throwError
    "no splittable hypothesis found"
  let scriptBuilder? :=
    mkScriptBuilder? input.options.generateScript $
      .ofTactic goals.size `(tactic| aesop_split_hyps)
  return (goals, scriptBuilder?, none)

end Aesop.BuiltinRules
