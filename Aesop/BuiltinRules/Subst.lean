/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute
import Aesop.RuleTac.Forward.Basic

open Lean Lean.Meta Aesop.Script

namespace Aesop.BuiltinRules

structure SubstitutableEq where
  fvarId : FVarId
  symm : Bool

inductive SubstitutableHyp
  | eq (h : SubstitutableEq)
  | iff (fvarId : FVarId) (eqProof eqType : Expr) (symm : Bool)

def getSubstitutableHyp (fvarId : FVarId) : MetaM (Option SubstitutableHyp) := do
  let ldecl ← fvarId.getDecl
  let ty ← instantiateMVars ldecl.type
  matchHelper? ty λ ty => do
    if let some (lhs, rhs) := ty.iff? then
      if ! (lhs.isFVar || rhs.isFVar) then
        return none
      let prf ← mkPropExt (.fvar fvarId)
      let type ← mkEq lhs rhs
      let symm := rhs.isFVar
      return some $ .iff fvarId (eqProof := prf) (eqType := type) symm
    else if let some (_, lhs, rhs) := ty.eq? then
      if ! (lhs.isFVar || rhs.isFVar) then
        return none
      let symm := rhs.isFVar
      return some $ .eq { fvarId, symm }
    else
      return none

def getSubstitutableEqs (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptM (MVarId × Array SubstitutableEq) := do
  let hyps ← goal.withContext $ fvarIds.mapM (getSubstitutableHyp ·)
  let mut eqs := Array.mkEmpty fvarIds.size
  let mut goal := goal
  for hyp in hyps do
    match hyp with
    | some (.eq e) => eqs := eqs.push e
    | some (.iff fvarId eqProof eqType symm) =>
      let (goal', newFVarId) ← replaceFVarS goal fvarId eqType eqProof
      goal := goal'
      eqs := eqs.push { fvarId := newFVarId, symm }
    | none => continue
  return (goal, eqs)

def substFVars (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptM (Option MVarId) := do
  let (goal, eqs) ← getSubstitutableEqs goal fvarIds
  let preGoal := goal
  let mut goal := goal
  let mut substitutedFVarIds := Array.mkEmpty fvarIds.size
  let mut fvarSubst : FVarSubst := {}
  let mut anySuccess := false
  let preState ← show MetaM _ from saveState
  for eq in eqs do
    let (.fvar fvarId) := fvarSubst.get eq.fvarId | throwError
      "unexpected expr in FVarSubst"
    let substResult? ← substCore? goal fvarId (symm := eq.symm) fvarSubst
    if let (some (fvarSubst', goal')) := substResult? then
      goal := goal'
      fvarSubst := fvarSubst'
      substitutedFVarIds := substitutedFVarIds.push eq.fvarId
      anySuccess := true
  if ! anySuccess then
    return none
  goal ← hideForwardImplDetailHyps goal -- HACK
  let postState ← show MetaM _ from saveState
  recordScriptStep {
    postGoals := #[goal]
    tacticBuilders := #[TacticBuilder.substFVars preGoal substitutedFVarIds]
    preGoal, preState, postState
  }
  return goal

@[aesop (rule_sets := [builtin]) norm -50 tactic (index := [hyp _ = _, hyp _ ↔ _])]
def subst : RuleTac := RuleTac.ofSingleRuleTac λ input =>
  input.goal.withContext do
    let hyps ← input.indexMatchLocations.toArray.mapM λ
      | .hyp ldecl => pure ldecl.fvarId
      | _ => throwError "unexpected index match location"
    let (some goal, steps) ← substFVars input.goal hyps |>.run
      | throwError "no suitable hypothesis found"
    -- TODO we can construct a better diff here, and doing so would be important
    -- since `subst` often renames fvars.
    let goal ← mvarIdToSubgoal input.goal goal ∅
    return (#[goal], steps, none)

end Aesop.BuiltinRules
