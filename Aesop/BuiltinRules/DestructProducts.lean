/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

private def destructProductHyp (goal : MVarId) (hyp : FVarId) :
    MetaM MVarId :=
  withMVarContext goal do
    let hypType ← instantiateMVars (← getLocalDecl hyp).type
    match hypType with
    | (.app (.app (.const ``And _ _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``And.casesOn [← mkFreshLevelMVar]) α β)
    | (.app (.app (.const ``Prod lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``Prod.casesOn  ((← mkFreshLevelMVar) :: lvls)) α β)
    | (.app (.app (.const ``PProd lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``PProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
    | (.app (.app (.const ``MProd lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``MProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
    | (.app (.app (.const ``Exists lvls _) α _) β _) => do
      go hypType (mkApp2 (mkConst ``Exists.casesOn lvls) α β)
    | (.app (.app (.const ``Subtype lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``Subtype.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
    | (.app (.app (.const ``Sigma lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``Sigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
    | (.app (.app (.const ``PSigma lvls _) α _) β _) =>
      go hypType (mkApp2 (mkConst ``PSigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
    | _ => return goal
  where
    -- `rec` is the partially applied recursor. Missing arguments to `rec` are
    -- the motive, the hypothesis and the new proof.
    go (hypType : Expr) (rec : Expr) : MetaM MVarId := do
      let (genHyps, goal) ← revert goal #[hyp] (preserveOrder := true)
      let (hyp, goal) ← intro1 goal
      let hypExpr := mkFVar hyp
      let tgt ← instantiateMVars (← getMVarType goal)
      let motive := mkLambda `h .default hypType $ tgt.abstract #[hypExpr]
      let prf := mkApp2 rec motive hypExpr
      withMVarContext goal $ check prf
      let [goal] ← apply goal prf
        | throwError "destructProducts: apply did not return exactly one goal"
      discard $ introN goal (genHyps.size - 1)
      let (_, goal) ← introN goal 2
      clear goal hyp

partial def destructProductsCore (goal : MVarId) : MetaM MVarId :=
  withMVarContext goal do
    let newGoal ← go 0 goal
    if newGoal == goal then
      throwError "destructProducts: found no hypothesis with a product-like type"
    else
      return newGoal
  where
    go (i : Nat) (goal : MVarId) : MetaM MVarId := do
      withMVarContext goal do
        let lctx ← getLCtx
        if i < lctx.decls.size then
          match lctx.decls[i] with
          | none => go (i + 1) goal
          | some ldecl =>
            if ldecl.isAuxDecl then
              go (i + 1) goal
            else
              let newGoal ← destructProductHyp goal ldecl.fvarId
              if newGoal == goal then
                go (i + 1) newGoal
              else
                go i newGoal
        else
          return goal

-- This tactic splits hypotheses of product-like types: `And`, `Prod`, `PProd`,
-- `MProd`, `Exists`, `Subtype`, `Sigma` and `PSigma`. It's a restricted version
-- of `cases`. We have this separate tactic because `cases` interacts badly with
-- metavariables and therefore can't be used for norm rules.
@[aesop norm 0
  (tactic (uses_branch_state := false)
    (index := [hyp And _ _, hyp Prod _ _, hyp PProd _ _, hyp MProd _ _,
               hyp Exists _, hyp Subtype _, hyp Sigma _, hyp PSigma _]))]
partial def destructProducts : RuleTac := λ input => do
  let goal ← destructProductsCore input.goal
  let mvars ← getGoalMVarsNoDelayed goal
  let postState ← saveState
  return {
    applications := #[{
      goals := #[(goal, mvars)]
      postState
      introducedMVars := {}
      assignedMVars := {}
    }]
    postBranchState? := none
  }

end Aesop.BuiltinRules
