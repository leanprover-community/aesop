/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

private def destructProductHyp? (goal : MVarId) (hyp : FVarId)
    (md : TransparencyMode) (generateScript : Bool) :
    MetaM (Option (MVarId × Option RuleTacScriptBuilder)) :=
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
        MetaM (MVarId × Option RuleTacScriptBuilder) := do
      let initialGoal := goal
      let initialHyp := hyp
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
      let scriptBuilder? := mkScriptBuilder? generateScript $
        let ctorNames :=
          #[{ ctor, args := #[lName, rName], hasImplicitArg := false }]
        .rcases initialGoal initialHyp ctorNames
      return (goal, scriptBuilder?)

partial def destructProductsCore (goal : MVarId) (md : TransparencyMode)
    (generateScript : Bool) : MetaM (MVarId × Option RuleTacScriptBuilder) :=
  goal.withContext do
    let result ← go 0 goal (mkScriptBuilder? generateScript .id)
    if result.fst == goal then
      throwError "destructProducts: found no hypothesis with a product-like type"
    return result
  where
    go (i : Nat) (goal : MVarId) (scriptBuilder? : Option RuleTacScriptBuilder) :
        MetaM (MVarId × Option RuleTacScriptBuilder) := do
      goal.withContext $ withIncRecDepth do
        let lctx ← getLCtx
        if h : i < lctx.decls.size then
          match lctx.decls[i] with
          | none => go (i + 1) goal scriptBuilder?
          | some ldecl =>
            if ldecl.isImplementationDetail then
              go (i + 1) goal scriptBuilder?
            else
              let result? ←
                destructProductHyp? goal ldecl.fvarId md generateScript
              if let some (newGoal, newScriptBuilder?) := result? then
                let scriptBuilder? :=
                  return (← scriptBuilder?).seq #[← newScriptBuilder?]
                go i newGoal scriptBuilder?
              else
                go (i + 1) goal scriptBuilder?
        else
          return (goal, scriptBuilder?)

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
  let (goal, scriptBuilder?) ←
    destructProductsCore input.goal md input.options.generateScript
  return (#[goal], scriptBuilder?, none)

end Aesop.BuiltinRules
