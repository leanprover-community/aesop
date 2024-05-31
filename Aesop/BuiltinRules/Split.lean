/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

private def renameInaccessibleFVars (goals : Array MVarId)
    (generateScript : Bool) :
    MetaM (Array MVarId × Array RuleTacScriptBuilder) := do
  let mut scriptBuilders := Array.mkEmpty goals.size
  let mut newGoals := Array.mkEmpty goals.size
  for goal in goals do
    let (goal, _, scriptBuilder?) ←
      renameInaccessibleFVarsWithScript goal generateScript
    newGoals := newGoals.push goal
    if let some scriptBuilder := scriptBuilder? then
      scriptBuilders := scriptBuilders.push scriptBuilder
  return (newGoals, scriptBuilders)

@[aesop (rule_sets := [builtin]) safe 100]
def splitTarget : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let generateScript := input.options.generateScript
  let (some goals) ← splitTarget? input.goal | throwError
    "nothing to split in target"
  let goals := goals.toArray
  let (renamedGoals, renameScriptBuilders) ←
    renameInaccessibleFVars goals generateScript
  let scriptBuilder? :=
    mkScriptBuilder? input.options.generateScript $
      ScriptBuilder.ofTactic goals.size `(tactic| split)
        |>.seq renameScriptBuilders
  return (renamedGoals, scriptBuilder?, none)

def splitFirstHypothesis (goal : MVarId) (generateScript : Bool) :
    MetaM (Option (Array MVarId × Option RuleTacScriptBuilder)) :=
  goal.withContext do
    for ldecl in ← getLCtx do
      if ! ldecl.isImplementationDetail then
        if let some goals ← splitLocalDecl? goal ldecl.fvarId then
          let goals := goals.toArray
          let (renamedGoals, renameScriptBuilders) ←
            renameInaccessibleFVars goals generateScript
          let scriptBuilder? := mkScriptBuilder? generateScript $
            ScriptBuilder.ofTactic goals.size
              `(tactic| split at $(mkIdent ldecl.userName):ident)
              |>.seq renameScriptBuilders
          return (renamedGoals, scriptBuilder?)
    return none

partial def splitHypothesesCore (goal : MVarId) (generateScript : Bool) :
    MetaM (Option (Array MVarId × Option RuleTacScriptBuilder)) :=
  withIncRecDepth do
  let some (goals, scriptBuilder?) ← splitFirstHypothesis goal generateScript
    | return none
  let mut subgoals := #[]
  let mut subgoalScriptBuilders := #[]
  for g in goals do
    let sub? ← splitHypothesesCore g generateScript
    if let some (subgoals', subgoalScriptBuilder?) := sub? then
      subgoals := subgoals ++ subgoals'
      if let some subgoalScriptBuilder := subgoalScriptBuilder? then
        subgoalScriptBuilders := subgoalScriptBuilders.push subgoalScriptBuilder
    else
      subgoals := subgoals.push g
  let scriptBuilder? := return (← scriptBuilder?).seq subgoalScriptBuilders
  return (subgoals, scriptBuilder?)

@[aesop (rule_sets := [builtin]) safe 1000]
def splitHypotheses : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some (goals, scriptBuilder?)) ←
    splitHypothesesCore input.goal input.options.generateScript
    | throwError "no splittable hypothesis found"
  return (goals, scriptBuilder?, none)

end Aesop.BuiltinRules
