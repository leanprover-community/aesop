/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta
open Std (HashSet)

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
private def prepareSubstHyp (goal : MVarId) (fvarId : FVarId) :
    MetaM (Option (MVarId × FVarId × Expr × Expr × Expr)) :=
  goal.withContext do
    let ty ← instantiateMVars $ ← fvarId.getType
    matchHelper? ty λ ty => do
      if let some (α, lhs, rhs) := ty.eq? then
        return some (goal, fvarId, α, lhs, rhs)
      else if let some (lhs, rhs) := ty.iff? then
        let (goal, fvarId) ← iffToEq goal fvarId lhs rhs
        return some (goal, fvarId, .sort .zero, lhs, rhs)
      else
        return none

partial def substFVars (goal : MVarId) (fvarIds : Array FVarId) :
    MetaM (Option (MVarId × FVarSubst)) := do
  let (goal, modified, fvarSubst) ← go 0 false {} goal
  return if modified then some (goal, fvarSubst) else none
  where
    go (i : Nat) (modified : Bool) (fvarSubst : FVarSubst) (goal : MVarId) :
        MetaM (MVarId × Bool × FVarSubst) :=
      goal.withContext do
        if h : i < fvarIds.size then
          let (.fvar fvarId) := fvarSubst.get $ fvarIds.get ⟨i, h⟩ | throwError
            "unexpected expr in FVarSubst"
          let some (goal, fvarId', _, lhs, _) ← prepareSubstHyp goal fvarId
            | go (i + 1) modified fvarSubst goal
          let fvarSubst :=
            if fvarId' == fvarId then
              fvarSubst
            else
              fvarSubst.insert fvarId (.fvar fvarId')
          match ← substCore? goal fvarId' (symm := ! lhs.isFVar) fvarSubst with
          | none =>
            go (i + 1) modified fvarSubst goal
          | some (fvarSubst, goal) =>
            go (i + 1) (modified := true) fvarSubst goal
        else
          return (goal, modified, fvarSubst)

@[aesop (rule_sets [builtin]) norm -50
  (tactic (uses_branch_state := false) (index := [hyp _ = _, hyp _ ↔ _]))]
def subst : RuleTac := SimpleRuleTac.toRuleTac λ input => do
  let hyps ← input.indexMatchLocations.toArray.mapM λ
    | .hyp ldecl => pure ldecl.fvarId
    | _ => throwError "unexpected index match location"
  let (some (goal, _)) ← substFVars input.goal hyps | throwError
    "no suitable hypothesis found"
  return [goal]
end Aesop.BuiltinRules
