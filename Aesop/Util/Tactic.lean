/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Lean.Meta.Tactic.Delta
import Aesop.Util.Basic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop

-- TODO This tactic simply executes the `MetaM` version of `cases`. We need this
-- when generating tactic scripts because the `MetaM` version and the `TacticM`
-- version of `cases` use different naming heuristics. If the two tactics were
-- harmonised, we could use regular `cases` in the script (assuming there are no
-- other differences).
elab "aesop_cases " x:ident : tactic =>
  liftMetaTactic λ goal => do
    let fvarId ← getFVarFromUserName x.getId
    let subgoals ← goal.cases fvarId.fvarId!
    return subgoals.map (·.mvarId) |>.toList

inductive UnfoldResult (α : Type)
  | unchanged
  | changed (new : α) (usedDecls : HashSet Name)

namespace UnfoldResult

def new? : UnfoldResult α → Option α
  | unchanged => none
  | changed x _ => some x

def usedDecls? : UnfoldResult α → Option (HashSet Name)
  | unchanged => none
  | changed _ usedDecls => some usedDecls

def usedDecls (r : UnfoldResult α) : HashSet Name :=
  r.usedDecls?.getD {}

end UnfoldResult

-- Inspired by Lean.Meta.unfold, Lean.Meta.unfoldTarget,
-- Lean.Meta.unfoldLocalDecl.

def mkUnfoldSimpContext : MetaM Simp.Context := do
  return {
    simpTheorems := #[]
    congrTheorems := ← getSimpCongrTheorems
    config := Simp.neutralConfig
    dischargeDepth := 0
  }

@[inline]
def unfoldManyCore (ctx : Simp.Context) (unfold? : Name → Option (Option Name))
    (e : Expr) : StateRefT (HashSet Name) MetaM Simp.Result :=
  λ usedDeclsRef =>
    (·.fst) <$> Simp.main e ctx (methods := { pre := (pre · usedDeclsRef) })
where
  -- NOTE: once we succeed in unfolding something, we return `done`. This
  -- means that `simp` won't recurse into the unfolded expression, missing
  -- potential further opportunities for unfolding.
  --
  -- I've tried returning
  -- `visit` instead, in which case we get recursive unfolding as desired, but
  -- we also get different results than when we call the `unfold` tactic
  -- multiple times.
  --
  -- Aesop calls `unfold` multiple times anyway, so the current implementation
  -- is slow but correct.
  pre (e : Expr) : StateRefT (HashSet Name) SimpM Simp.Step := do
    let some decl := e.getAppFn'.constName?
      | return .continue
    match unfold? decl with
    | none =>
      return .continue
    | some none =>
      if let some e' ← delta? e (λ n => n == decl) then
        modify (·.insert decl)
        return .done { expr := e' }
      else
        return .continue
    | some (some unfoldThm) =>
      let result? ← withReducible <| Simp.withDischarger (fun _ => return none) <|
        Simp.tryTheorem? e
          { origin := .decl unfoldThm
            proof := mkConst unfoldThm
            rfl := ← isRflTheorem unfoldThm }
      match result? with
      | none   => return .continue
      | some r =>
        modify (·.insert decl)
        match (← reduceMatcher? r.expr) with
        | .reduced e' => return .done { r with expr := e' }
        | _ => return .done r

def unfoldMany (unfold? : Name → Option (Option Name)) (e : Expr) :
    MetaM (UnfoldResult Expr) := do
  let e ← instantiateMVars e
  let (r, usedDecls) ← unfoldManyCore (← mkUnfoldSimpContext) unfold? e |>.run {}
  if (← instantiateMVars r.expr) == e then
    return .unchanged
  else
    return .changed r.expr usedDecls

def unfoldManyStar (goal : MVarId)
    (unfold? : Name → Option (Option Name)) : MetaM (UnfoldResult MVarId) :=
  goal.withContext do
    let initialGoal := goal
    let mut goal := goal
    let usedDeclsRef ← IO.mkRef {}
    let ctx ← mkUnfoldSimpContext

    let target ← instantiateMVars (← goal.getType)
    let r ← unfoldManyCore ctx unfold? target usedDeclsRef
    if (← instantiateMVars r.expr) != target then
      goal ← applySimpResultToTarget goal target r

    for ldecl in (← goal.getDecl).lctx do
      let r ←
        unfoldManyCore ctx unfold? (← instantiateMVars ldecl.type) usedDeclsRef
      if (← instantiateMVars r.expr) != ldecl.type then
        let some (_, goal') ←
          applySimpResultToLocalDecl goal ldecl.fvarId r (mayCloseGoal := false)
          | throwTacticEx `aesop_unfold goal "internal error: unexpected result of applySimpResultToLocalDecl"
        goal := goal'

    if goal == initialGoal then
      return .unchanged
    else
      return .changed goal (← usedDeclsRef.get)

elab "aesop_unfold " "[" ids:ident,+ "]" : tactic => do
  let mut toUnfold : HashMap Name (Option Name) := {}
  for id in (ids : Array Ident) do
    let decl ← resolveGlobalConstNoOverload id
    toUnfold := toUnfold.insert decl (← getUnfoldEqnFor? decl)

  liftMetaTactic λ goal => do
    match ← unfoldManyStar goal (toUnfold.find? ·) with
    | .unchanged =>
      throwTacticEx `aesop_unfold goal "could not unfold any of the given constants"
    | .changed goal _ => return [goal]

end Aesop
