/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.RuleTac.Forward.Basic

open Lean Lean.Meta Aesop.Script

namespace Aesop.BuiltinRules

def matchSubstitutableIff? (e : Expr) : Option (Expr × Expr) := do
  let some (lhs, rhs) := e.iff?
    | failure
  if lhs.isFVar || rhs.isFVar then
    return (lhs, rhs)
  else
    failure

def prepareIff? (mvarId : MVarId) (fvarId : FVarId) :
    ScriptM (Option (MVarId × FVarId)) :=
  mvarId.withContext do
    let ty ← fvarId.getType
    let some (lhs, rhs) ← matchHelper? ty (pure ∘ matchSubstitutableIff?)
      | return none
    let eqPrf ← mkPropExt (.fvar fvarId)
    let eqType ← mkEq lhs rhs
    let preState ← show MetaM _ from saveState
    let (newMVarId, newFVarId, clearSuccess) ←
      replaceFVarS mvarId fvarId eqType eqPrf
    if ! clearSuccess then
      preState.restore
      return none
    return some (newMVarId, newFVarId)

def prepareIffs (mvarId : MVarId) (fvarIds : Array FVarId) :
    ScriptM (MVarId × Array FVarId) := do
  let mut mvarId := mvarId
  let mut newFVarIds := Array.mkEmpty fvarIds.size
  for fvarId in fvarIds do
    if let some (newMVarId, newFVarId) ← prepareIff? mvarId fvarId then
      mvarId := newMVarId
      newFVarIds := newFVarIds.push newFVarId
    else
      newFVarIds := newFVarIds.push fvarId
  return (mvarId, newFVarIds)

def substEqs? (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptM (Option MVarId) := do
  let preGoal := goal
  let preState ← show MetaM _ from saveState
  let userNames ← goal.withContext do fvarIds.mapM (·.getUserName)
  let mut goal := goal
  let mut substitutedUserNames := Array.mkEmpty userNames.size
  for userName in userNames do
    let ldecl ← goal.withContext $ getLocalDeclFromUserName userName
    if let some goal' ← subst? goal ldecl.fvarId then
      goal := goal'
      substitutedUserNames := substitutedUserNames.push userName
  if goal == preGoal then
    return none
  goal ← hideForwardImplDetailHyps goal -- HACK
  let postState ← show MetaM _ from saveState
  recordScriptStep {
    postGoals := #[goal]
    tacticBuilders := #[TacticBuilder.substFVars' substitutedUserNames]
    preGoal, preState, postState
  }
  return goal

def substEqsAndIffs? (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptM (Option MVarId) := do
  let preState ← show MetaM _ from saveState
  let (goal, fvarIds) ← prepareIffs goal fvarIds
  if let some goal ← substEqs? goal fvarIds then
    return goal
  else
    preState.restore
    return none

@[aesop (rule_sets := [builtin]) norm -50 tactic (index := [hyp _ = _, hyp _ ↔ _])]
def subst : RuleTac := RuleTac.ofSingleRuleTac λ input =>
  input.goal.withContext do
    let hyps ← input.indexMatchLocations.toArray.mapM λ
      | .hyp ldecl => pure ldecl.fvarId
      | _ => throwError "unexpected index match location"
    let (some goal, steps) ← substEqsAndIffs? input.goal hyps |>.run
      | throwError "no suitable hypothesis found"
    -- TODO we can construct a better diff here, and doing so would be important
    -- since `subst` often renames fvars.
    let goal ← mvarIdToSubgoal input.goal goal ∅
    return (#[goal], steps, none)

end Aesop.BuiltinRules
