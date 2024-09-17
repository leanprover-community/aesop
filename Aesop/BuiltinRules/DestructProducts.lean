/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean Lean.Meta Aesop.Script

namespace Aesop.BuiltinRules

private def destructProductHyp? (goal : MVarId) (hyp : FVarId)
    (md : TransparencyMode) : MetaM (Option (LazyStep × MVarId)) :=
  goal.withContext do
    let hypType ← hyp.getType
    let (f, args) ← withTransparency md $ getAppUpToDefeq hypType
    match args with
    | #[α, β] =>
      match f with
      | (.const ``And _) =>
        go hypType (.const ``And.casesOn [← mkFreshLevelMVar]) α β
          ``And.intro `left `right
      | (.const ``Prod lvls) =>
        go hypType (.const ``Prod.casesOn  ((← mkFreshLevelMVar) :: lvls)) α β
          ``Prod.mk `fst `snd
      | (.const ``PProd lvls) =>
        go hypType (.const ``PProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β
          ``PProd.mk `fst `snd
      | (.const ``MProd lvls) =>
        go hypType (.const ``MProd.casesOn ((← mkFreshLevelMVar) :: lvls)) α β
          ``MProd.mk `fst `snd
      | (.const ``Exists lvls) =>
        go hypType (.const ``Exists.casesOn lvls) α β ``Exists.intro `w `h
      | (.const ``Subtype lvls) =>
        go hypType (.const ``Subtype.casesOn ((← mkFreshLevelMVar) :: lvls)) α β
          ``Subtype.mk `val `property
      | (.const ``Sigma lvls) =>
        go hypType (.const ``Sigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β
          ``Sigma.mk `fst `snd
      | (.const ``PSigma lvls) =>
        go hypType (.const ``PSigma.casesOn ((← mkFreshLevelMVar) :: lvls)) α β
          ``PSigma.mk `fst `snd
      | _ => return none
    | _ => return none
  where
    -- `rec` is the partially applied recursor. Missing arguments to `rec` are
    -- the motive, the hypothesis and the new proof.
    go (hypType rec lType rType : Expr) (ctor lName rName : Name) :
        MetaM (LazyStep × MVarId) := do
      let (step, mvarId, _) ← LazyStep.build goal {
        tac := tac hypType rec lType rType lName rName
        postGoals := (#[·.1])
        tacticBuilder := λ (_, lName, rName) =>
          TacticBuilder.obtain goal (.fvar hyp)
            { ctor, args := #[lName, rName], hasImplicitArg := false }
      }
      return (step, mvarId)

    tac (hypType rec lType rType : Expr) (lName rName : Name) :
        MetaM (MVarId × Name × Name) := do
      let (genHyps, goal) ← goal.revert #[hyp] (preserveOrder := true)
      let (hyp, goal) ← intro1Core goal (preserveBinderNames := true)
      let hypExpr := mkFVar hyp
      let tgt ← instantiateMVars (← goal.getType)
      let motive := mkLambda `h .default hypType $ tgt.abstract #[hypExpr]
      let prf := mkApp4 rec lType rType motive hypExpr
      goal.withContext $ check prf
      let [goal] ← goal.apply prf
        | throwError "destructProducts: apply did not return exactly one goal"
      let goal ← goal.clear hyp
      let lctx := (← goal.getDecl).lctx
      -- The following is only valid if `lName` and `rName` are distinct.
      -- Otherwise they could yield two identical unused names.
      let lName := lctx.getUnusedName lName
      let rName := lctx.getUnusedName rName
      let (_, goal) ← goal.introN 2 [lName, rName]
      let (_, goal) ← introNCore goal (genHyps.size - 1) []
        (preserveBinderNames := true) (useNamesForExplicitOnly := false)
      return (goal, lName, rName)

partial def destructProductsCore (goal : MVarId) (md : TransparencyMode) :
    MetaM (MVarId × Array LazyStep) := do
  let result ← go 0 goal |>.run
  if result.fst == goal then
    throwError "destructProducts: found no hypothesis with a product-like type"
  return result
where
  go (i : Nat) (goal : MVarId) : ScriptM MVarId := do
    withIncRecDepth $ goal.withContext do
      let lctx ← getLCtx
      if h : i < lctx.decls.size then
        match lctx.decls[i] with
        | none => go (i + 1) goal
        | some ldecl =>
          if ldecl.isImplementationDetail then
            go (i + 1) goal
          else
            let result? ← destructProductHyp? goal ldecl.fvarId md
            if let some (newScriptStep, newGoal) := result? then
              recordScriptStep newScriptStep
              go i newGoal
            else
              go (i + 1) goal
      else
        return goal

-- This tactic splits hypotheses of product-like types: `And`, `Prod`, `PProd`,
-- `MProd`, `Exists`, `Subtype`, `Sigma` and `PSigma`. It's a restricted version
-- of `cases`. We have this separate tactic because `cases` interacts badly with
-- metavariables and therefore can't be used for norm rules.
--
-- NOTE: If `destructProductsTransparency` != `.reducible`, then this rule is
-- moved from the by-hyp index to the unindexed rules. The rule is identified by
-- name, so if you change its name, you must also adjust the function
-- responsible for dynamically unindexing rules.
@[aesop norm 0 (rule_sets := [builtin]) tactic
    (index := [hyp And _ _, hyp Prod _ _, hyp PProd _ _, hyp MProd _ _,
               hyp Exists _, hyp Subtype _, hyp Sigma _, hyp PSigma _])]
partial def destructProducts : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let md := input.options.destructProductsTransparency
  let (goal, steps) ← destructProductsCore input.goal md
  -- TODO we can construct a better diff here, and it would be important to do
  -- so because `destructProducts` often renames hypotheses.
  let goal := { mvarId := goal, diff := ← diffGoals input.goal goal ∅ }
  return (#[goal], steps, none)

end Aesop.BuiltinRules
