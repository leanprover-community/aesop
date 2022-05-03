/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleTac

partial def cases (decl : Name) (isRecursiveType : Bool) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => do
    let goals? ← go #[] #[] input.goal
    match goals? with
    | none => throwError "No hypothesis of type {decl} found"
    | some goals => return goals.toList
  where
    findFirstApplicableHyp (excluded : Array FVarId) (goal : MVarId) :
        MetaM (Option FVarId) :=
      withMVarContext goal do
        return (← getLCtx).findDecl? λ ldecl =>
          if ! ldecl.isAuxDecl &&
             ldecl.type.isAppOf decl &&
             ! excluded.contains ldecl.fvarId then
          -- Note: We currently check for occurrences of `decl` structurally,
          -- not up to WHNF.
            some ldecl.fvarId
          else
            none

    go (newGoals : Array MVarId) (excluded : Array FVarId)
        (goal : MVarId) : MetaM (Option (Array MVarId)) := do
      let (some hyp) ← findFirstApplicableHyp excluded goal
        | return none
      try
        let goals ← Meta.cases goal hyp
        let mut newGoals := newGoals
        for g in goals do
          let excluded :=
            if ! isRecursiveType then
              excluded
            else
              let excluded := excluded.map λ fvarId =>
                match g.subst.find? fvarId with
                | some (Expr.fvar fvarId' ..) => fvarId'
                | _ => fvarId
              excluded ++ g.fields.map (·.fvarId!)
          let newGoals? ← go newGoals excluded g.mvarId
          match newGoals? with
          | some newGoals' => newGoals := newGoals'
          | none => newGoals := newGoals.push g.mvarId
        return some newGoals
      catch e =>
        return none

end Aesop.RuleTac
