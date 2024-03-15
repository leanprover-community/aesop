/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop safe -50 (rule_sets := [builtin])]
def assumption : RuleTac := λ input => do
  let goal := input.goal
  let md := input.options.assumptionTransparency
  goal.withContext do
    goal.checkNotAssigned `Aesop.BuiltinRules.assumption
    goal.instantiateMVars
    let tgt ← goal.getType
    let tgtHasMVar := tgt.hasMVar
    let initialState ← saveState
    let mut applications := #[]
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      restoreState initialState
      let (some (application, proofHasMVar)) ← tryHyp goal ldecl.fvarId md
        | continue
      if ! tgtHasMVar && ! proofHasMVar then
        applications := #[application]
        break
      else
        applications := applications.push application
    if applications.isEmpty then
      throwTacticEx `Aesop.BuiltinRules.assumption goal "no matching assumption found"
    return ⟨applications⟩
  where
    tryHyp (goal : MVarId) (fvarId : FVarId) (md : TransparencyMode) :
        MetaM (Option (RuleApplication × Bool)) := do
      let (true, steps) ← tryExactFVarS goal fvarId md |>.run
        | return none
      let #[step] := steps
        | throwError "aesop: internal error in assumption: multiple steps"
      let proofHasMVar := (← fvarId.getType).hasMVar
      let app := {
        goals := #[]
        postState := step.postState
        scriptSteps? := #[step]
        successProbability? := none
      }
      return some (app, proofHasMVar)

end Aesop.BuiltinRules
