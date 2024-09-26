import Lean

open Lean Std Lean.Meta

namespace Aesop

structure GoalWithMVars where
  goal : MVarId
  mvars : Std.HashSet MVarId
  deriving Inhabited

instance : Repr GoalWithMVars where
  reprPrec
    | g, _ => s!"\{ goal := {repr g.goal}, mvars := {repr g.mvars.toArray} }"

instance : BEq GoalWithMVars :=
  ⟨λ g₁ g₂ => g₁.goal == g₂.goal⟩

namespace GoalWithMVars

def ofMVarId (goal : MVarId) : MetaM GoalWithMVars := do
  return { goal, mvars := ← goal.getMVarDependencies }

end Aesop.GoalWithMVars
