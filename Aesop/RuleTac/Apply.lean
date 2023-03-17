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
    (generateScript : Bool) : MetaM (Array MVarId × Option RuleTacScriptBuilder) := do
  let goals := (← goal.apply e).toArray
  let scriptBuilder? :=
    mkScriptBuilder? generateScript $
      .ofTactic goals.size `(tactic| apply $(mkIdent n))
  return (goals, scriptBuilder?)

def applyConst (decl : Name) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input => do
    applyExpr input.goal (← mkConstWithFreshMVarLevels decl) decl
      input.options.generateScript

def applyFVar (userName : Name) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input =>
    input.goal.withContext do
      applyExpr input.goal (← getLocalDeclFromUserName userName).toExpr
        userName input.options.generateScript

-- Tries to apply each constant in `decls`. For each one that applies, a rule
-- application is returned. If none applies, the tactic fails.
def applyConsts (decls : Array Name) : RuleTac := λ input => do
  let initialState ← saveState
  let generateScript := input.options.generateScript
  let apps ← decls.filterMapM λ decl => do
    try
      let e ← mkConstWithFreshMVarLevels decl
      let (goals, scriptBuilder?) ← applyExpr input.goal e decl generateScript
      let postState ← saveState
      return some { postState, goals, scriptBuilder? }
    catch _ =>
      return none
    finally
      restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any of these declarations:{MessageData.node $ decls.map toMessageData}"
  return ⟨apps⟩

end RuleTac
