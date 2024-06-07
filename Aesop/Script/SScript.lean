import Aesop.Script.Step

open Lean Lean.Meta

variable [Monad m] [MonadError m] [MonadQuotation m]

namespace Aesop.Script

inductive SScript
  | empty
  | onGoal (goalPos : Nat) (step : Step) (tail : SScript)
  | focusAndSolve (goalPos : Nat) (here tail : SScript)
  deriving Inhabited

namespace SScript

def render (script : SScript) : m (Array Syntax.Tactic) := do
  go #[] script
  where
    go (acc : Array Syntax.Tactic) :
        SScript → m (Array Syntax.Tactic)
      | empty => return acc
      | onGoal goalPos step tail => do
        let script := acc.push $ mkOnGoal goalPos step.uTactic
        go script tail
      | focusAndSolve goalPos here tail => do
        let nestedScript ← go #[] here
        let t ←
          if goalPos == 0 then
            `(tactic| · $[$nestedScript:tactic]*)
          else
            let posLit := mkOneBasedNumLit goalPos
            `(tactic| on_goal $posLit:num => { $nestedScript:tactic* })
        go (acc.push t) tail

end Aesop.Script.SScript
