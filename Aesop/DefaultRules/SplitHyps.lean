/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Rule.Tac

open Lean

namespace Aesop.DefaultRules.SplitHyps

-- We define the `splitHyp` tactic, which splits hypotheses that are products
-- or existentials. It recurses into nested products, so `A ∧ B ∧ C` is split
-- into three hypotheses with types `A`, `B` and `C`. It also works under
-- binders, so `h : ∀ x, P x ∧ Q x` is split into `h₁ : ∀ x, P x` and
-- `h₂ : ∀ x, Q x`.
--
-- Exception: `Exists`, unlike `Sigma` and `PSigma`, cannot be split under
-- binders. This is unavoidable: `∀ (x : X), ∃ (y : Y), P y` does not imply
-- `∃ (f : X → Y), ∀ x, P (f x)` in Lean's logic.

-- TODO The splitHyps tactic currently does not handle existentials with
-- products nested in the witness. E.g. the hypothesis
--
--   h : ∃ (p : X × Y), P p
--
-- is decomposed into
--
--   h₁ : X × Y
--   h₂ : P h₁
--
-- when it should really be
--
--   h₁ : X
--   h₂ : Y
--   h₃ : P (h₁, h₂)
--
-- To fix this, we should canonicalise such hypotheses before splitting them.
-- The canonicalisation would make sure the witness is not a product by
-- rewriting, e.g.,
--
--   ∃ (p : X × Y), P p           ↝ ∃ (x : X) (y : Y), P (x, y)
--   ∃ (p : ∃ (x : X), P x), Q p  ↝ ∃ (x : X) (y : P x), Q (Exists.intro x y)
--
-- @[simp]
-- theorem exists_prod {X Y} (P : X × Y → Prop) :
--     (∃ (p : X × Y), P p) ↔ ∃ (x : X) (y : Y), P (x, y) :=
--   Iff.intro
--     (λ ⟨⟨x, y⟩, Pp⟩ => ⟨x, y, Pp⟩)
--     (λ ⟨x, y, Pxy⟩ => ⟨⟨x, y⟩, Pxy⟩)
--
-- We could also use this implementation strategy for splitting under binders:
-- rewrite `∀ x, P x ∧ Q x` into `(∀ x, P x) ∧ (∀ x, Q x)`. This would reduce
-- the implementation complexity a lot, though at some performance cost.

open Expr
open Lean.Meta

partial def splitHypCore (goal : MVarId) (originalUserName : Name)
    (binderFVars : Array Expr) (hyp : FVarId) (type : Expr) :
    MetaM (Array FVarId × MVarId) :=
  match type with
  | forallE .. => do
    forallTelescope type λ binders conclusion =>
      splitHypCore goal originalUserName (binderFVars ++ binders) hyp conclusion
  | app (app (const ``And lvls _) leftType _) rightType _ =>
    splitProduct goal (mkConst ``And.left lvls) (mkConst ``And.right lvls)
      leftType rightType
  | app (app (const ``Prod lvls _) leftType _) rightType _ =>
    splitProduct goal (mkConst ``Prod.fst lvls) (mkConst ``Prod.snd lvls)
      leftType rightType
  | app (app (const ``PProd lvls _) leftType _) rightType _ =>
    splitProduct goal (mkConst ``PProd.fst lvls) (mkConst ``PProd.snd lvls)
      leftType rightType
  | app (app (const ``MProd lvls _) leftType _) rightType _ =>
    splitProduct goal (mkConst ``MProd.fst lvls) (mkConst ``MProd.snd lvls)
      leftType rightType
  | app (app (const ``Sigma lvls _) witnessType _) propertyType _ => do
    splitExistential goal (mkConst ``Sigma.fst lvls) (mkConst ``Sigma.snd lvls)
      witnessType propertyType
  | app (app (const ``PSigma lvls _) witnessType _) propertyType _ => do
    splitExistential goal (mkConst ``PSigma.fst lvls) (mkConst ``PSigma.snd lvls)
      witnessType propertyType
  | app (app (const ``Exists lvls _) witnessType _) propertyType _ => do
    -- We can't eliminate Exists under binders.
    if ¬ binderFVars.isEmpty then
      return (#[], goal)
    let #[casesGoal] ← cases goal hyp
      | unreachable!
    pure (casesGoal.fields.map (·.fvarId!), casesGoal.mvarId)
  | _ => pure (#[], goal)
  where
    hypWithBinderFVars : Expr :=
      mkAppN (mkFVar hyp) binderFVars

    splitProductHalf (goal : MVarId) (left : Bool)
        (eliminator leftType rightType : Expr) : MetaM (FVarId × MVarId) := do
      let type := if left then leftType else rightType
      let newHypType ← mkForallFVars binderFVars type
      let newHypProof ← mkLambdaFVars binderFVars $
        mkAppN eliminator #[leftType, rightType, hypWithBinderFVars]
      let goal ← assert goal originalUserName newHypType newHypProof
      let (newHyp, goal) ← intro1 goal
      return (newHyp, goal)

    splitProduct (goal : MVarId)
        (leftEliminator rightEliminator leftType rightType : Expr) :
        MetaM (Array FVarId × MVarId) := do
      let (leftHyp, goal) ←
        splitProductHalf goal true  leftEliminator  leftType rightType
      let (rightHyp, goal) ←
        splitProductHalf goal false rightEliminator leftType rightType
      let (goal, cleared) :=
        match (← observing? $ clear goal hyp) with
        | none => (goal, false)
        | some goal => (goal, true)
      let (leftHyps, goal)  ←
        splitHypCore goal originalUserName binderFVars leftHyp  leftType
      let (rightHyps, goal) ←
        splitHypCore goal originalUserName binderFVars rightHyp rightType
      let newHyps :=
        if cleared
          then leftHyps ++ rightHyps
          else (leftHyps ++ rightHyps).push hyp
      return (newHyps, goal)

    splitExistential (oldGoal : MVarId)
        (witnessProjection propertyProjection witnessType propertyType : Expr) :
        MetaM (Array FVarId × MVarId) := do

      checkNotAssigned goal `splitHyp
      let tag ← getMVarTag goal
      let oldTarget ← getMVarType goal

      -- I don't see how to make `assert` work with successive dependent
      -- hypotheses, so here's a reimplementation. We assert one hypothesis for
      -- the witness and one for the property, where the property hypothesis
      -- depends on the witness hypothesis.
      let witnessHypType ← mkForallFVars binderFVars witnessType
      let newTarget ← do
        withLocalDeclD originalUserName witnessHypType λ witness => do
          let propertyHypType ←
            mkForallFVars binderFVars $
            (← headBeta (mkApp propertyType (mkAppN witness binderFVars)))
          withLocalDeclD originalUserName propertyHypType λ property =>
            mkForallFVars (#[witness, property]) oldTarget
      let goal ← withMVarContext goal $
        mkFreshExprSyntheticOpaqueMVar newTarget tag

      let witnessHypProof ← mkLambdaFVars binderFVars $
        mkAppN witnessProjection #[witnessType, propertyType, hypWithBinderFVars]
      let propertyHypProof ← mkLambdaFVars binderFVars $
        mkAppN propertyProjection #[witnessType, propertyType, hypWithBinderFVars]
      let proof := mkAppN goal #[witnessHypProof, propertyHypProof]
      assignExprMVar oldGoal proof

      let goal := goal.mvarId!
      let (#[witnessHyp, propertyHyp], goal) ← introN goal 2 | unreachable!

      let (goal, cleared) :=
        match (← observing? $ clear goal hyp) with
        | none => (goal, false)
        | some goal => (goal, true)
      let propertyHypTypeWithoutBinders ←
        headBeta (mkApp propertyType $ mkAppN (mkFVar witnessHyp) binderFVars)
      let (newHyps, goal) ←
        splitHypCore goal originalUserName binderFVars propertyHyp
          propertyHypTypeWithoutBinders
      let newHyps :=
        if cleared then newHyps else newHyps.push hyp
      return (newHyps, goal)

def splitHyp (goal : MVarId) (hyp : FVarId) : MetaM (Array FVarId × MVarId) := do
  checkNotAssigned goal `Aesop.DefaultRules.SplitHyps.splitHyp
  withMVarContext goal do
    let decl ← getLocalDecl hyp
    splitHypCore goal decl.userName #[] hyp decl.type

def splitHyps (goal : MVarId) : MetaM (Array FVarId × MVarId) := do
  checkNotAssigned goal `Aesop.DefaultRules.SplitHyps.splitHyps
  let lctx := (← getMVarDecl goal).lctx
  let mut goal := goal
  let mut newHypsList := Array.mkEmpty lctx.decls.size
  let mut numNewHyps := 0
  for localDecl in lctx do
    if localDecl.isAuxDecl then continue
    let (newHyps, goal') ← splitHyp goal localDecl.fvarId
    newHypsList := newHypsList.push newHyps
    numNewHyps := numNewHyps + newHyps.size
    goal := goal'
  let newHyps := newHypsList.foldl (init := Array.mkEmpty numNewHyps) (· ++ ·)
  return (newHyps, goal)

end SplitHyps

def splitHyps : SimpleRuleTac := λ input =>
  return { regularGoals := #[(← SplitHyps.splitHyps input.goal).snd] }

end Aesop.DefaultRules
