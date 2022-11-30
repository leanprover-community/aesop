/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

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
elab &"aesop_cases" x:ident : tactic =>
  liftMetaTactic λ goal => do
    let fvarId ← getFVarFromUserName x.getId
    let subgoals ← goal.cases fvarId.fvarId!
    return subgoals.map (·.mvarId) |>.toList

inductive UnfoldResult
  | unchanged
  | changed (goal : MVarId) (usedDecls : HashSet Name)

namespace UnfoldResult

def newGoal? : UnfoldResult → Option MVarId
  | unchanged => none
  | changed goal _ => some goal

def usedDecls? : UnfoldResult → Option (HashSet Name)
  | unchanged => none
  | changed _ usedDecls => some usedDecls

def usedDecls (r : UnfoldResult) : HashSet Name :=
  r.usedDecls?.getD {}

end UnfoldResult


def mkUnfoldSimpContext : MetaM Simp.Context := do
  return {
    simpTheorems := #[]
    congrTheorems := ← getSimpCongrTheorems
    config := Simp.neutralConfig
    dischargeDepth := 0
  }

-- Inspired by Lean.Meta.unfold, Lean.Meta.unfoldTarget,
-- Lean.Meta.unfoldLocalDecl.
def _root_.Lean.MVarId.unfoldManyStar (goal : MVarId)
    (unfold? : Name → Option (Option Name)) : MetaM UnfoldResult :=
  goal.withContext do
    let initialGoal := goal
    let mut goal := goal
    let usedDecls ← IO.mkRef {}
    let ctx ← mkUnfoldSimpContext

    let target ← instantiateMVars (← goal.getType)
    let r ← unfold usedDecls ctx target
    if (← instantiateMVars r.expr) != target then
      goal ← applySimpResultToTarget goal target r

    for ldecl in (← goal.getDecl).lctx do
      let r ← unfold usedDecls ctx (← instantiateMVars ldecl.type)
      if (← instantiateMVars r.expr) != ldecl.type then
        let some (_, goal') ←
          applySimpResultToLocalDecl goal ldecl.fvarId r (mayCloseGoal := false)
          | unreachable!
        goal := goal'

    if goal == initialGoal then
      return .unchanged
    else
      return .changed goal (← usedDecls.get)
  where
    @[inline]
    unfold (usedDecls : IO.Ref (HashSet Name)) (ctx : Simp.Context) (e : Expr) :
        MetaM Simp.Result :=
      (·.fst) <$>
        Simp.main e ctx (methods := { pre := pre usedDecls })

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
    pre (usedDecls : IO.Ref (HashSet Name)) (e : Expr) : SimpM Simp.Step := do
      let some decl := e.getAppFn'.constName?
        | return .visit { expr := e }
      match unfold? decl with
      | none =>
        return .visit { expr := e }
      | some none =>
        if let some e' ← delta? e (λ n => n == decl) then
          usedDecls.modify (·.insert decl)
          return .done { expr := e' }
        else
          return .visit { expr := e }
      | some (some unfoldThm) =>
        let result? ← withReducible <|
          Simp.tryTheorem? e
            { origin := .decl unfoldThm
              proof := mkConst unfoldThm
              rfl := ← isRflTheorem unfoldThm }
            (fun _ => return none)
        match result? with
        | none   => return .visit { expr := e }
        | some r =>
          usedDecls.modify (·.insert decl)
          match (← reduceMatcher? r.expr) with
          | .reduced e' => return .done { r with expr := e' }
          | _ => return .done r

elab &"aesop_unfold " "[" ids:ident,+ "]" : tactic => do
  let mut toUnfold : HashMap Name (Option Name) := {}
  for id in (ids : Array Ident) do
    let decl ← resolveGlobalConstNoOverload id
    toUnfold := toUnfold.insert decl (← getUnfoldEqnFor? decl)

  liftMetaTactic λ goal => do
    match ← goal.unfoldManyStar (toUnfold.find? ·) with
    | .unchanged =>
      throwTacticEx `aesop_unfold goal "could not unfold any of the given constants"
    | .changed goal _ => return [goal]

end Aesop
