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

partial def substFVars (goal : MVarId) (fvarIds : Array FVarId) :
    MetaM (Option (MVarId × FVarSubst)) := do
  let (goal, modified, fvarSubst) ← go 0 false {} goal
  return if modified then some (goal, fvarSubst) else none
  where
    go (i : Nat) (modified : Bool) (fvarSubst : FVarSubst) (goal : MVarId) :
        MetaM (MVarId × Bool × FVarSubst) :=
      withMVarContext goal do
        if h : i < fvarIds.size then
          let (.fvar fvarId) := fvarSubst.get $ fvarIds.get ⟨i, h⟩ | throwError
            "unexpected expr in FVarSubst"
          let type ← instantiateMVars (← getLocalDecl fvarId).type
          let (some (_, lhs, _)) ← matchEq? type
            | go (i + 1) modified fvarSubst goal
          let symm := ! lhs.isFVar
          match ← substCore? goal fvarId (symm := symm) fvarSubst with
          | none =>
            go (i + 1) modified fvarSubst goal
          | some (fvarSubst, goal) =>
            go (i + 1) (modified := true) fvarSubst goal
        else
          return (goal, modified, fvarSubst)

@[aesop (rule_sets [builtin]) norm -50
  (tactic (uses_branch_state := false) (index := [hyp _ = _]))]
def subst : RuleTac := λ input => do
  let hyps ← input.indexMatchLocations.toArray.mapM λ
    | .hyp ldecl => pure ldecl.fvarId
    | _ => throwError "unexpected index match location"
  let (some (goal, _)) ← substFVars input.goal hyps | throwError
    "no suitable hypothesis found"
  let postState ← saveState
  return {
    applications := #[{ goals := #[goal], postState }],
    postBranchState? := none
  }
end Aesop.BuiltinRules
