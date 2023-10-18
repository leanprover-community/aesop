/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleTac

private def applyExpr (goal : MVarId) (e : Expr) (n : Name)
    (md : TransparencyMode) (generateScript : Bool) :
    MetaM (Array MVarId × Option RuleTacScriptBuilder × Option Percent) := do
  let goals := (← withTransparency md $ goal.apply e).toArray
  let scriptBuilder? :=
    mkScriptBuilder? generateScript $
      .ofTactic goals.size do
        withAllTransparencySyntax md (← `(tactic| apply $(mkIdent n)))
  return (goals, scriptBuilder?, none)

def applyConst (decl : Name) (md : TransparencyMode) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input => do
    applyExpr input.goal (← mkConstWithFreshMVarLevels decl) decl md
      input.options.generateScript

def applyFVar (userName : Name) (md : TransparencyMode) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input =>
    input.goal.withContext do
      applyExpr input.goal (← getLocalDeclFromUserName userName).toExpr
        userName md input.options.generateScript

-- Tries to apply each constant in `decls`. For each one that applies, a rule
-- application is returned. If none applies, the tactic fails.
def applyConsts (decls : Array Name) (md : TransparencyMode) :
    RuleTac := λ input => do
  let initialState ← saveState
  let generateScript := input.options.generateScript
  let apps ← decls.filterMapM λ decl => do
    try
      let e ← mkConstWithFreshMVarLevels decl
      let (goals, scriptBuilder?, successProbability?) ←
        applyExpr input.goal e decl md generateScript
      let postState ← saveState
      return some { postState, goals, scriptBuilder?, successProbability? }
    catch _ =>
      return none
    finally
      restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any of these declarations:{decls}"
  return ⟨apps⟩

end RuleTac
