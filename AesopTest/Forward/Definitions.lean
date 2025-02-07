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
