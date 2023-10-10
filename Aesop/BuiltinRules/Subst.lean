/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

private def iffToEq (goal : MVarId) (fvarId : FVarId) (lhs : Expr)
    (rhs : Expr) : MetaM (MVarId × FVarId) := do
  let newType ← mkEq lhs rhs
  let proof ← mkPropExt (.fvar fvarId)
  let goal ← goal.assert (← fvarId.getUserName) newType proof
  let (newFVarId, goal) ← goal.intro1P
  let goal ← goal.tryClear fvarId
  return (goal, newFVarId)

-- If the `fvarId` is an `Iff`, it is turned into an `Eq`. If the `fvarId` is an
-- `Eq`, it is returned unchanged. Additionally, the type, LHS and RHS of the
-- resulting equation are returned.
private def prepareSubstHyp (goal : MVarId) (fvarId : FVarId)
    (fvarSubst : FVarSubst) :
    MetaM (Option (MVarId × FVarId × Expr × Expr × Expr × FVarSubst)) :=
  goal.withContext do
    let ty ← instantiateMVars $ ← fvarId.getType
    matchHelper? ty λ ty => do
      if let some (α, lhs, rhs) := ty.eq? then
        return some (goal, fvarId, α, lhs, rhs, fvarSubst)
      else if let some (lhs, rhs) := ty.iff? then
        let (goal, fvarId') ← iffToEq goal fvarId lhs rhs
        let fvarSubst := fvarSubst.insert fvarId (mkFVar fvarId')
        return some (goal, fvarId', .sort .zero, lhs, rhs, fvarSubst)
      else
        return none

partial def substFVars (goal : MVarId) (fvarIds : Array FVarId) :
    MetaM (MVarId × Array Name × FVarSubst) := do
  let mut goal := goal
  let mut fvarSubst := {}
  let mut substitutedHypNames := Array.mkEmpty fvarIds.size
  for h : i in [:fvarIds.size] do
    let (.fvar fvarId) := fvarSubst.get $ fvarIds[i]'h.2 | throwError
      "unexpected expr in FVarSubst"
    let hypName ← goal.withContext fvarId.getUserName
    let some (goal', fvarId', _, lhs, _, fvarSubst') ←
      prepareSubstHyp goal fvarId fvarSubst
      | continue
    goal := goal'
    fvarSubst := fvarSubst'
    let substResult? ← substCore? goal fvarId' (symm := ! lhs.isFVar) fvarSubst
    if let (some (fvarSubst', goal')) := substResult? then
      goal := goal'
      fvarSubst := fvarSubst'
      substitutedHypNames := substitutedHypNames.push hypName
  return (goal, substitutedHypNames, fvarSubst)

open Lean.Elab.Tactic in
def elabAesopSubst (hyps : Array Syntax.Ident) : TacticM Unit := do
  liftMetaTactic λ goal => do
    let fvars ← hyps.mapM λ id =>
      return (← getLocalDeclFromUserName id.getId).fvarId
    let (goal, substitutedUserNames, _) ← substFVars goal fvars
    if substitutedUserNames.size == 0 then
      throwTacticEx `aesop_subst goal
        "failed to substitute any of the given hypotheses"
    else
      return [goal]

elab "aesop_subst " "[" hyps:ident,+ "]" : tactic =>
  elabAesopSubst hyps

elab "aesop_subst " hyp:ident : tactic =>
  elabAesopSubst #[hyp]

@[aesop (rule_sets [builtin]) norm -50
    (tactic (index := [hyp _ = _, hyp _ ↔ _]))]
def subst : RuleTac := RuleTac.ofSingleRuleTac λ input =>
  input.goal.withContext do
    let hyps ← input.indexMatchLocations.toArray.mapM λ
      | .hyp ldecl => pure ldecl.fvarId
      | _ => throwError "unexpected index match location"
    let (goal, substitutedUserNames, _) ← substFVars input.goal hyps
    if substitutedUserNames.size == 0 then
      throwError "no suitable hypothesis found"
    let scriptBuilder? :=
      mkScriptBuilder? input.options.generateScript $
        let substitutedUserNames := substitutedUserNames.map mkIdent
        let tactic :=
          if h : substitutedUserNames.size = 1 then
            let hypName := substitutedUserNames[0]'(by rw [h]; decide)
            `(tactic| aesop_subst $hypName)
          else
            `(tactic| aesop_subst [ $substitutedUserNames:ident,* ])
        .ofTactic 1 tactic
    return (#[goal], scriptBuilder?, none)

end Aesop.BuiltinRules
