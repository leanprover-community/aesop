/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Kaiyu Yang
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM evalTactic run)

namespace Aesop.RuleTac

-- Precondition: `decl` has type `TacticM Unit`.
unsafe def tacticMImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
    let goals ← run input.goal tac |>.run'
    return (goals.toArray, none, none)

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

-- Precondition: `decl` has type `TacGen`.
unsafe def tacGenImpl (decl : Name) : RuleTac := λ input => do
  let tacGen ← evalConst TacGen decl
  let initialState ← saveState
  let suggestions ← tacGen input.goal
  let mut apps := Array.mkEmpty suggestions.size
  let mut errors : Array (String × Exception) := Array.mkEmpty suggestions.size
  for (tacticStr, successProbability) in suggestions do
    initialState.restore
    let env ← getEnv
    try
      let some successProbability := Percent.ofFloat successProbability
        | throwError "invalid success probability '{successProbability}', must be between 0 and 1"
      let .ok stx :=
        Parser.runParserCategory env `tactic tacticStr (fileName := "<stdin>")
        | throwError "failed to parse tactic syntax{indentD tacticStr}"
      let goals := (← run input.goal (evalTactic stx) |>.run').toArray
      let postState ← saveState
      if let some proof ← getExprMVarAssignment? input.goal then
        if (← instantiateMVars proof).hasSorry then
          throwError "generated proof contains sorry"
      let scriptBuilder? :=
        mkScriptBuilder? input.options.generateScript $
          .ofTactic goals.size (return ⟨stx⟩)
      apps := apps.push {
        successProbability? := some successProbability
        goals, postState, scriptBuilder?
      }
    catch e =>
      errors := errors.push (tacticStr, e)
  if apps.isEmpty then throwError
    "Failed to apply any tactics generated. Errors:{indentD $ MessageData.joinSep (errors.toList.map (λ (tac, e) => m!"{tac}: {e.toMessageData}")) "\n"}"
  return ⟨apps⟩

-- Precondition: `decl` has type `TacGen`.
@[implemented_by tacGenImpl]
opaque tacGen (decl : Name) : RuleTac

end Aesop.RuleTac
