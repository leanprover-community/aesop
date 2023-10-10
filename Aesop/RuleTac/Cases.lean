/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop

-- NOTE: introduces fresh metavariables for the 'holes' in `p`.
def CasesPattern.toExpr (p : CasesPattern) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult p
  return p

inductive CasesTarget' where
  | decl (decl : Name)
  | patterns (ps : Array (Expr × Meta.SavedState))

def CasesTarget.toCasesTarget' : CasesTarget → MetaM CasesTarget'
  | decl d => return .decl d
  | patterns ps => withoutModifyingState do
    let initialState ← saveState
    .patterns <$> ps.mapM λ p => do
      initialState.restore
      let e ← p.toExpr
      let s ← saveState
      return (e, s)

namespace RuleTac

partial def cases (target : CasesTarget) (md : TransparencyMode) (isRecursiveType : Bool) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    match ← go #[] #[] input.goal input.options.generateScript with
    | none => throwError "No matching hypothesis found."
    | some (goals, scriptBuilder?) => return (goals, scriptBuilder?, none)
  where
    findFirstApplicableHyp (excluded : Array FVarId) (goal : MVarId) :
        MetaM (Option FVarId) :=
      withTransparency md do goal.withContext do
        let target ← target.toCasesTarget'
        let «match» ldecl : MetaM Bool :=
          match target with
          | .decl d => do
            isAppOfUpToDefeq (← mkConstWithFreshMVarLevels d) ldecl.type
          | .patterns ps => withoutModifyingState do
            ps.anyM λ (e, state) => do state.restore; isDefEq e ldecl.type
        return ← (← getLCtx).findDeclM? λ ldecl => do
          if ldecl.isImplementationDetail || excluded.contains ldecl.fvarId then
            return none
          else if ← «match» ldecl then
            return some ldecl.fvarId
          else
            return none

    go (newGoals : Array MVarId) (excluded : Array FVarId)
        (goal : MVarId) (generateScript : Bool) :
        MetaM (Option (Array MVarId × Option RuleTacScriptBuilder)) := do
      let (some hyp) ← findFirstApplicableHyp excluded goal
        | return none
      let (goals, scriptBuilder?) ←
        try
          commitIfNoEx $ unhygienicCasesWithScript goal hyp generateScript
        catch _ =>
          return none
      let mut newGoals := newGoals
      let mut newScriptBuilders := #[]
      for g in goals do
        let excluded :=
          if ! isRecursiveType then
            excluded
          else
            let excluded := excluded.map λ fvarId =>
              match g.subst.find? fvarId with
              | some (.fvar fvarId' ..) => fvarId'
              | _ => fvarId
            let fields := g.fields.filterMap λ
              | (.fvar fvarId' ..) => some fvarId'
              | _ => none
            excluded ++ fields
        match ← go newGoals excluded g.mvarId generateScript with
        | some (newGoals', newScriptBuilder?) =>
          newGoals := newGoals'
          if let some newScriptBuilder := newScriptBuilder? then
            newScriptBuilders := newScriptBuilders.push newScriptBuilder
        | none =>
          newGoals := newGoals.push g.mvarId
          if generateScript then
            newScriptBuilders := newScriptBuilders.push .id
      return some (newGoals, scriptBuilder?.bind (·.seq newScriptBuilders))

end Aesop.RuleTac
