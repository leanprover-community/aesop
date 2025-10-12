import Aesop

open Aesop
open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

inductive SNat where
  | zero
  | succ (n : SNat)

abbrev Nat.toSNat : Nat → SNat
  | zero => .zero
  | succ n => .succ n.toSNat

elab "snat% " n:num : term => do
  let n ← elabTerm n (some $ .const ``Nat [])
  reduceAll (.app (.const ``Nat.toSNat []) n)

instance : MonadBacktrack Core.SavedState CoreM where
  saveState := Core.saveState
  restoreState := Core.SavedState.restore

initialize timeRef : IO.Ref Nanos ← IO.mkRef 0

elab "time " t:tactic : tactic => do
  let nanos ← Aesop.time' $ Lean.Elab.Tactic.evalTactic t
  timeRef.set nanos

/-- A benchmark that can be run by the `bchmk` command. -/
structure Benchmark where
  /-- A title for the benchmark's output. -/
  title : String
  /-- A function that executes the benchmark once. -/
  fn : Nat → CommandElabM Nanos
