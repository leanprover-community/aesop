/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta
open Lean.Elab.Term (TermElabM withSynthesize)
open Lean.Elab.Tactic (TacticM evalTactic run)

namespace Aesop.RuleTac

-- Precondition: `decl` has type `TacticM Unit`.
unsafe def tacticMImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
    let goals ← run input.goal tac |>.run'
    return (goals.toArray, none)

-- Precondition: `decl` has type `TacticM Unit`.
@[implemented_by tacticMImpl]
opaque tacticM (decl : Name) : RuleTac

-- Precondition: `decl` has type `RuleTac`.
unsafe def ruleTacImpl (decl : Name) : RuleTac := λ input => do
  let tac ← evalConst RuleTac decl
  tac input

-- Precondition: `decl` has type `RuleTac`.
@[implemented_by ruleTacImpl]
opaque ruleTac (decl : Name) : RuleTac

-- Precondition: `decl` has type `SimpleRuleTac`.
unsafe def singleRuleTacImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SingleRuleTac decl
    tac input

-- Precondition: `decl` has type `SimpleRuleTac`.
@[implemented_by singleRuleTacImpl]
opaque singleRuleTac (decl : Name) : RuleTac

-- Precondition: `decl` has type `MVarId → MetaM (Array (String × Float))`.
unsafe def tacGenImpl (decl : Name) : RuleTac := λ input => do
  let tac ← evalConst (MVarId → MetaM (Array (String × Float))) decl
  let initialState ← saveState
  let suggestions ← tac input.goal
  let apps ← suggestions.filterMapM fun (tacticStr, score) => do
    assert! 0 ≤ score ∧ score ≤ 1   
    match Parser.runParserCategory (← getEnv) `tactic tacticStr (fileName := "<stdin>") with
    | .error _ => return none
    | .ok stx =>
      try 
        initialState.restore
        let tac := commitIfNoEx $ evalTactic stx
        -- let tstx : TSyntax `tactic := {raw := stx}
        let goals ← run input.goal tac |>.run'
        let pf? ← getExprMVarAssignment? input.goal
        if pf?.isSome then
          if (← instantiateMVars pf?.get!) |>.hasSorry then 
            initialState.restore
            return none
        -- let scriptBuilder? :=
        --   mkScriptBuilder? generateScript $
        --     .ofTactic goals.toArray.size do
        --       withAllTransparencySyntax md tstx
        let postState ← saveState
        let thisApp : RuleApplication := {
          postState := postState
          goals := goals.toArray
          probabilityModifier := score
          -- scriptBuilder? := scriptBuilder?
          scriptBuilder? := none
        }
        return thisApp
      catch _ => pure none
  restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any tactics generated"
  return ⟨apps⟩

-- Precondition: `decl` has type `MVarId → MetaM (Array (String × Float))`.
@[implemented_by tacGenImpl]
opaque tacGen (decl : Name) : RuleTac

end Aesop.RuleTac
