/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop

namespace CasesPattern

-- NOTE: introduces fresh metavariables for the 'holes' in `p`.
def toExpr (p : CasesPattern) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult p
  return p

end CasesPattern


namespace RuleTac

partial def cases (target : CasesTarget) (isRecursiveType : Bool) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    match ← go #[] #[] input.goal input.options.generateScript with
    | none => throwError "No matching hypothesis found."
    | some x => return x
  where
    findFirstApplicableHyp (excluded : Array FVarId) (goal : MVarId) :
        MetaM (Option FVarId) :=
      goal.withContext do
        let «match» ldecl : MetaM Bool :=
          match target with
          | .decl d => withoutModifyingState do
            return (← matchAppOf (← mkConstWithFreshMVarLevels d) ldecl.type).isSome
          | .patterns ps => ps.anyM λ p => withoutModifyingState do
              isDefEq (← p.toExpr) ldecl.type
              -- TODO `p.toExpr` is mildly expensive, so it would be nicer if
              -- we didn't have to do this all the time. But we must be careful
              -- not to leak metavariables.
        return ← (← getLCtx).findDeclM? λ ldecl => do
          if ← (pure $ ! ldecl.isAuxDecl) <&&>
             «match» ldecl <&&>
             pure (! excluded.contains ldecl.fvarId) then
            return some ldecl.fvarId
          else
            return none

    go (newGoals : Array MVarId) (excluded : Array FVarId) (goal : MVarId)
        (generateScript : Bool) : MetaM (Option (Array MVarId × Option RuleTacScriptBuilder)) := do
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
