/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Kaiyu Yang
-/

import Aesop.RuleTac.Basic
import Aesop.Script.Step

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM evalTactic run)

namespace Aesop.RuleTac

-- Precondition: `decl` has type `TacticM Unit`.
unsafe def tacticMImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
    let goals ← run input.goal tac |>.run'
    let goals ← goals.mapM (mvarIdToSubgoal (parentMVarId := input.goal) · ∅)
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

/--
Elaborates and runs the given tactic syntax `stx`. The syntax `stx` must be of
kind `tactic` or `tacticSeq`.
-/
def tacticStx (stx : Syntax) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let preState ← saveState
    let postGoals := (← run input.goal (evalTactic stx) |>.run').toArray
    let postState ← saveState
    let tacticBuilder : Script.TacticBuilder := do
      if stx.isOfKind `tactic then
        return .unstructured ⟨stx⟩
      else if stx.isOfKind ``Parser.Tactic.tacticSeq then
        let stx := ⟨stx⟩
        (.unstructured ·) <$> `(tactic| ($stx:tacticSeq))
      else
        throwError "expected either a single tactic or a sequence of tactics"
    let step := {
      preGoal := input.goal
      tacticBuilders := #[tacticBuilder]
      preState, postState, postGoals
    }
    let postGoals ←
      postGoals.mapM (mvarIdToSubgoal (parentMVarId := input.goal) · ∅)
    return (postGoals, some #[step], none)

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
      let postGoals := (← run input.goal (evalTactic stx) |>.run').toArray
      let postState ← saveState
      if let some proof ← getExprMVarAssignment? input.goal then
        if ← hasSorry proof then
          throwError "generated proof contains sorry"
      let step := {
        preState := initialState
        preGoal := input.goal
        tacticBuilders := #[return .unstructured ⟨stx⟩]
        postState, postGoals
      }
      let postGoals ←
        postGoals.mapM (mvarIdToSubgoal (parentMVarId := input.goal) · ∅)
      apps := apps.push {
        goals := postGoals
        scriptSteps? := some #[step]
        successProbability? := successProbability
        postState
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
