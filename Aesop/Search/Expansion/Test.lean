import Aesop.Search.Expansion.Norm
import Lean.Meta
open Lean Meta
--NVU
/-
def setupGoal : IO MVarId := do
  let goalType := mkConst`Nat
  let goalExpr ← mkFreshExprMVar goalType
  return goalExpr.mvarId

def testReduceAllInGoal : MetaM Bool := do
  let goal ← setupGoal
  let originalType ← goal.getType
  let reducedGoal ← reduceAllInGoal goal
  let newType ← reducedGoal.getType
  return originalType ≠ newType

def runTest : IO Unit := do
  let env ← MetaM.run testReduceAllInGoal
  if env then
    IO.println "Test passed: Goal was reduced."
  else
    IO.println "Test failed: Goal was not reduced."
-/

abbrev Foo := Nat

run_meta show MetaM Unit from do
  let goal ← Lean.Meta.mkFreshExprMVar (mkConst `Nat)
  logInfo m!"Generated goal: {goal}"

example : Foo := by
  run_tac do
    let e <- Elab.Tactic.getMainTarget
    let e' <- reduceAll e
    logInfo e'
  exact 1


abbrev Bopo := Nat

run_meta show MetaM Unit from do
  let goal ← Lean.Meta.mkFreshExprMVar (mkConst `Bool)
  logInfo m!"Generated goal: {goal}"

example : Bopo := by
  run_tac do
    let e <- Elab.Tactic.getMainTarget
    let e' <- reduceAll e
    logInfo e'
  exact 5
