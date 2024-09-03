/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic
import Aesop.RuleTac.ElabRuleTerm
import Aesop.Script.SpecificTactics

open Lean
open Lean.Meta
open Lean.PrettyPrinter (delab)

namespace Aesop.RuleTac

def applyExpr' (goal : MVarId) (e : Expr) (eStx : Term)
    (pat? : Option RulePattern) (patInst : RulePatternInstantiation)
    (md : TransparencyMode) : MetaM RuleApplication :=
  withTransparency md do
    let e ←
      if let some pat := pat? then
        pat.specializeRule patInst e
      else
        pure e
    let (goals, #[step]) ← applyS goal e eStx md |>.run
      | throwError "aesop: internal error in applyExpr': multiple steps"
    let goals := goals.map λ mvarId => { mvarId, diff := ∅ }
    return {
      goals
      postState := step.postState
      scriptSteps? := #[step]
      successProbability? := none
    }

def applyExpr (goal : MVarId) (e : Expr) (eStx : Term)
    (pat? : Option RulePattern) (patInsts : Std.HashSet RulePatternInstantiation)
    (md : TransparencyMode) : MetaM RuleTacOutput := do
  if pat?.isSome then
    let mut rapps := Array.mkEmpty patInsts.size
    let initialState ← saveState
    for patInst in patInsts do
      try
        let rapp ← applyExpr' goal e eStx pat? patInst md
        rapps := rapps.push rapp
      catch _ =>
        continue
      finally
        restoreState initialState
    if rapps.isEmpty then
      throwError "failed to apply '{e}' with any of the matched instances of the rule pattern"
    return { applications := rapps }
  else
    let rapp ← applyExpr' goal e eStx none ∅ md
    return { applications := #[rapp] }

def applyConst (decl : Name) (pat? : Option RulePattern)
    (md : TransparencyMode) : RuleTac := λ input => do
  applyExpr input.goal (← mkConstWithFreshMVarLevels decl) (mkIdent decl) pat?
    input.patternInstantiations md

def applyTerm (stx : Term) (pat? : Option RulePattern) (md : TransparencyMode) :
    RuleTac :=
  λ input => input.goal.withContext do
    applyExpr input.goal (← elabRuleTermForApplyLikeMetaM input.goal stx) stx
      pat? input.patternInstantiations md

def apply (t : RuleTerm) (pat? : Option RulePattern) (md : TransparencyMode) :
    RuleTac :=
  match t with
  | .const decl => applyConst decl pat? md
  | .term tm => applyTerm tm pat? md

-- Tries to apply each constant in `decls`. For each one that applies, a rule
-- application is returned. If none applies, the tactic fails.
def applyConsts (decls : Array Name) (md : TransparencyMode) :
    RuleTac := λ input => do
  let initialState ← saveState
  let apps ← decls.filterMapM λ decl => do
    try
      let e ← mkConstWithFreshMVarLevels decl
      some <$> applyExpr' input.goal e (mkIdent decl) none ∅ md
    catch _ =>
      return none
    finally
      restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any of these declarations: {decls}"
  return ⟨apps⟩

end RuleTac
