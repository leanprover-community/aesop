/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean Lean.Meta

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

def getSubstitutableEqs (goal : MVarId) (fvarIds : Array FVarId)
    (generateScript : Bool) :
    MetaM (MVarId × Array SubstitutableEq × Option RuleTacScriptBuilder) := do
  let hyps ← goal.withContext $ fvarIds.mapM getSubstitutableHyp
  let mut eqs := Array.mkEmpty fvarIds.size
  let mut goal := goal
  let mut scriptBuilder? : Option RuleTacScriptBuilder := some .id
  for hyp in hyps do
    match hyp with
    | some (.eq e) => eqs := eqs.push e
    | some (.iff fvarId eqProof eqType symm) =>
      let (goal', newFVarId, replaceScriptBuilder?) ←
        replaceFVarWithScript goal fvarId eqType eqProof generateScript
      goal := goal'
      eqs := eqs.push { fvarId := newFVarId, symm }
      scriptBuilder? := return (← scriptBuilder?).seq #[← replaceScriptBuilder?]
    | none => continue
  return (goal, eqs, scriptBuilder?)

def substFVars (goal : MVarId) (fvarIds : Array FVarId) (generateScript : Bool) :
    MetaM (MVarId × Array Name × Option RuleTacScriptBuilder) := do
  let (goal, eqs, replaceScriptBuilder?) ←
    getSubstitutableEqs goal fvarIds generateScript
  let preGoal := goal
  let mut goal := goal
  let mut substitutedHypNames := Array.mkEmpty fvarIds.size
  let mut fvarSubst : FVarSubst := {}
  for eq in eqs do
    let (.fvar fvarId) := fvarSubst.get eq.fvarId | throwError
      "unexpected expr in FVarSubst"
    let hypName ← goal.withContext fvarId.getUserName
    let substResult? ← substCore? goal eq.fvarId (symm := eq.symm) fvarSubst
    if let (some (fvarSubst', goal')) := substResult? then
      goal := goal'
      fvarSubst := fvarSubst'
      substitutedHypNames := substitutedHypNames.push hypName
  let substScriptBuilder? := mkScriptBuilder? generateScript $
    .ofTactics 1 $ preGoal.withContext do
      return #[← `(tactic| subst $(substitutedHypNames.map mkIdent):ident*)]
  let scriptBuilder? :=
    return (← replaceScriptBuilder?).seq #[← substScriptBuilder?]
  return (goal, substitutedHypNames, scriptBuilder?)

@[aesop (rule_sets := [builtin]) norm -50 tactic (index := [hyp _ = _, hyp _ ↔ _])]
def subst : RuleTac := RuleTac.ofSingleRuleTac λ input =>
  input.goal.withContext do
    let hyps ← input.indexMatchLocations.toArray.mapM λ
      | .hyp ldecl => pure ldecl.fvarId
      | _ => throwError "unexpected index match location"
    let (goal, substitutedUserNames, scriptBuilder?) ←
      substFVars input.goal hyps input.options.generateScript
    if substitutedUserNames.size == 0 then
      throwError "no suitable hypothesis found"
    return (#[goal], scriptBuilder?, none)

end Aesop.BuiltinRules
