/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

private def destructProductHyp (goal : MVarId) (hyp : FVarId)
    (md : TransparencyMode) : MetaM MVarId :=
  goal.withContext do
    let hypType ← hyp.getType
    let (f, args) ← withTransparency md $ getAppUpToDefeq hypType
    match args with
    | #[α, β] =>
      match f with
      | (.const ``And _) =>
        go hypType (mkApp2 (.const ``And.casesOn [← mkFreshLevelMVar]) α β)
      | (.const ``Prod lvls) =>
        go hypType (mkApp2 (.const ``Prod.casesOn  ((← mkFreshLevelMVar) :: lvls)) α β)
      | (.const ``PProd lvls) =>
        go hypType (mkApp2 (.const ``PProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
      | (.const ``MProd lvls) =>
        go hypType (mkApp2 (.const ``MProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
      | (.const ``Exists lvls) =>
        go hypType (mkApp2 (.const ``Exists.casesOn lvls) α β)
      | (.const ``Subtype lvls) =>
        go hypType (mkApp2 (.const ``Subtype.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
      | (.const ``Sigma lvls) =>
        go hypType (mkApp2 (.const ``Sigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
      | (.const ``PSigma lvls) =>
        go hypType (mkApp2 (.const ``PSigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β)
      | _ => return goal
    | _ => return goal
  where
    -- `rec` is the partially applied recursor. Missing arguments to `rec` are
    -- the motive, the hypothesis and the new proof.
    go (hypType : Expr) (rec : Expr) : MetaM MVarId := do
      let (genHyps, goal) ← goal.revert #[hyp] (preserveOrder := true)
      let (hyp, goal) ← goal.intro1
      let hypExpr := mkFVar hyp
      let tgt ← instantiateMVars (← goal.getType)
      let motive := mkLambda `h .default hypType $ tgt.abstract #[hypExpr]
      let prf := mkApp2 rec motive hypExpr
      goal.withContext $ check prf
      let [goal] ← goal.apply prf
        | throwError "destructProducts: apply did not return exactly one goal"
      let (_, goal) ← goal.introN (genHyps.size - 1)
      let (_, goal) ← goal.introN 2
      goal.clear hyp

partial def destructProductsCore (goal : MVarId) (md : TransparencyMode) :
    MetaM MVarId :=
  goal.withContext do
    let newGoal ← go 0 goal
    if newGoal == goal then
      throwError "destructProducts: found no hypothesis with a product-like type"
    else
      return newGoal
  where
    go (i : Nat) (goal : MVarId) : MetaM MVarId := do
      goal.withContext $ withIncRecDepth do
        let lctx ← getLCtx
        if h : i < lctx.decls.size then
          match lctx.decls[i] with
          | none => go (i + 1) goal
          | some ldecl =>
            if ldecl.isImplementationDetail then
              go (i + 1) goal
            else
              let newGoal ← destructProductHyp goal ldecl.fvarId md
              if newGoal == goal then
                go (i + 1) newGoal
              else
                go i newGoal
        else
          return goal

elab "aesop_destruct_products" : tactic =>
  Elab.Tactic.liftMetaTactic1 λ goal =>
    return some (← destructProductsCore goal (← getTransparency))

-- This tactic splits hypotheses of product-like types: `And`, `Prod`, `PProd`,
-- `MProd`, `Exists`, `Subtype`, `Sigma` and `PSigma`. It's a restricted version
-- of `cases`. We have this separate tactic because `cases` interacts badly with
-- metavariables and therefore can't be used for norm rules.
--
-- NOTE: If `destructProductsTransparency` != `.reducible`, then this rule is
-- moved from the by-hyp index to the unindexed rules. The rule is identified by
-- name, so if you change its name, you must also adjust the function
-- responsible for dynamically unindexing rules.
@[aesop norm 0 (rule_sets [builtin])
  (tactic
    (index := [hyp And _ _, hyp Prod _ _, hyp PProd _ _, hyp MProd _ _,
               hyp Exists _, hyp Subtype _, hyp Sigma _, hyp PSigma _]))]
partial def destructProducts : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let md := input.options.destructProductsTransparency
  let goal ← unhygienic $ destructProductsCore input.goal md
  let scriptBuilder? :=
    mkScriptBuilder? input.options.generateScript $ .ofTactic 1 do
      let tac ← withTransparencySyntax md (← `(tactic| aesop_destruct_products))
      `(tactic| unhygienic $tac:tactic)
  return (#[goal], scriptBuilder?, none)

end Aesop.BuiltinRules
