import LeanInfer

import Aesop.RuleTac.Basic

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Tactic

namespace Aesop.RuleTac

-- Tries to apply each tactic suggested by a neural network. For each one that
-- applies, a rule application is returned. If none applies, the tactic fails.
def applyNeural: RuleTac := λ input => do
  let initialState ← saveState
  let iptGoal ← LeanInfer.ppTacticState [input.goal]
  let optSuggestions ← LeanInfer.generate iptGoal
  let suggestions := optSuggestions.map (·.1)
  let apps ← suggestions.filterMapM λ tacticStr => do
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
          -- scriptBuilder? := scriptBuilder?
          scriptBuilder? := none
        }
        return thisApp
      catch _ => pure none
  restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any tactics generated"
  return ⟨apps⟩


end RuleTac

          

          