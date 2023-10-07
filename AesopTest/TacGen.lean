import Aesop

open Lean
open Lean.Meta

theorem foo (a b c : Nat) : a + b + c = c + b + a := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm]
  rw [Nat.add_comm b]

-- @[aesop unsafe 50% tactic]
-- def x (_ : MVarId) : MetaM (Array (String × Float)) := do
--  return #[("apply foo", 1.0)]

-- It wouldn't work without this.
@[aesop unsafe 80% tactic]
def x : MVarId → MetaM (Array (String × Float)) := fun _ => do
  return #[("rw [Nat.add_comm b]", 0.5), ("rw [Nat.add_assoc]", 0.9), ("rw [Nat.add_comm]", 0.8)]

example (a b c : Nat) : a + b + c = c + b + a := by
  aesop
