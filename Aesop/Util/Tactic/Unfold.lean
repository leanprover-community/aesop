/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Meta Lean.Elab.Tactic

namespace Aesop

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
    (e : Expr) : StateRefT (Array Name) MetaM Simp.Result :=
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
  pre (e : Expr) : StateRefT (Array Name) SimpM Simp.Step := do
    let some decl := e.getAppFn'.constName?
      | return .continue
    match unfold? decl with
    | none =>
      return .continue
    | some none =>
      if let some e' ← delta? e (λ n => n == decl) then
        modify (·.push decl)
        return .done { expr := e' }
      else
        return .continue
    | some (some unfoldThm) =>
      let result? ← withReducible <|
        Simp.tryTheorem? e
          { origin := .decl unfoldThm
            proof := mkConst unfoldThm
            rfl := ← isRflTheorem unfoldThm }
      match result? with
      | none   => return .continue
      | some r =>
        modify (·.push decl)
        match (← reduceMatcher? r.expr) with
        | .reduced e' => return .done { r with expr := e' }
        | _ => return .done r

def unfoldMany (unfold? : Name → Option (Option Name)) (e : Expr) :
    MetaM (Option (Expr × Array Name)) := do
  let e ← instantiateMVars e
  let (r, usedDecls) ← unfoldManyCore (← mkUnfoldSimpContext) unfold? e |>.run {}
  if (← instantiateMVars r.expr) == e then
    return none
  else
    return some (r.expr, usedDecls)

def unfoldManyTarget (unfold? : Name → Option (Option Name)) (goal : MVarId) :
    MetaM (Option (MVarId × Array Name)) := do
  let tgt ← instantiateMVars $ ← goal.getType
  let (result, usedDecls) ←
    unfoldManyCore (← mkUnfoldSimpContext) unfold? tgt |>.run #[]
  if result.expr == tgt then
    return none
  let goal ← applySimpResultToTarget goal tgt result
  return some (goal, usedDecls)

def unfoldManyAt (unfold? : Name → Option (Option Name)) (goal : MVarId)
    (fvarId : FVarId) : MetaM (Option (MVarId × Array Name)) :=
  goal.withContext do
    let type ← instantiateMVars $ ← fvarId.getType
    let (result, usedDecls) ←
      unfoldManyCore (← mkUnfoldSimpContext) unfold? type |>.run #[]
    if result.expr == type then
      return none
    let some (_, goal) ←
        applySimpResultToLocalDecl goal fvarId result (mayCloseGoal := false)
      | throwTacticEx `aesop_unfold goal "internal error: unexpected result of applySimpResultToLocalDecl"
    return some (goal, usedDecls)

def unfoldManyStar (unfold? : Name → Option (Option Name)) (goal : MVarId) :
    MetaM (Option MVarId) :=
  goal.withContext do
    let initialGoal := goal
    let mut goal := goal
    if let some (goal', _) ← unfoldManyTarget unfold? goal then
      goal := goal'
    for ldecl in (← goal.getDecl).lctx do
      if ldecl.isImplementationDetail then
        continue
      if let some (goal', _) ← unfoldManyAt unfold? goal ldecl.fvarId then
        goal := goal'
    if goal == initialGoal then
      return none
    else
      return some goal

private def mkToUnfold (ids : Array Ident) :
    MetaM (Std.HashMap Name (Option Name)) := do
  let mut toUnfold : Std.HashMap Name (Option Name) := {}
  for id in (ids : Array Ident) do
    let decl ← resolveGlobalConstNoOverload id
    toUnfold := toUnfold.insert decl (← getUnfoldEqnFor? decl)
  return toUnfold

elab "aesop_unfold " ids:ident+ : tactic => do
  let toUnfold ← mkToUnfold ids
  liftMetaTactic λ goal => do
    match ← unfoldManyTarget (toUnfold[·]?) goal with
    | none => throwTacticEx `aesop_unfold goal "could not unfold any of the given constants"
    | some (goal, _) => return [goal]

elab "aesop_unfold " ids:ident+ " at " hyps:ident+ : tactic => do
  let toUnfold ← mkToUnfold ids
  liftMetaTactic λ goal => do
    let mut goal := goal
    for hypId in hyps do
      let fvarId := (← getLocalDeclFromUserName hypId.getId).fvarId
      match ← unfoldManyAt (toUnfold[·]?) goal fvarId with
      | none => throwTacticEx `aesop_unfold goal m!"could not unfold any of the given constants at hypothesis '{hypId}'"
      | some (goal', _) => goal := goal'
    return [goal]

end Aesop
