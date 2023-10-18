import Aesop

open Lean
open Lean.Meta

theorem foo (a b c : Nat) : a + b + c = c + b + a := by
  rw [Nat.add_assoc, Nat.add_comm, Nat.add_comm b]

@[aesop 100%]
def tacGen₁ : Aesop.TacGen := λ _ => do
 return #[("apply foo", 1.0)]

example (a b c : Nat) : a + b + c = c + b + a := by
  aesop

@[aesop 100%]
def tacGen₂ : Aesop.TacGen := λ _ =>
  return #[
    ("rw [Nat.add_comm b]", 0.5),
    ("rw [Nat.add_assoc]", 0.9),
    ("rw [Nat.add_comm]", 0.8)
  ]

example (a b c : Nat) : a + b + c = c + b + a := by
  aesop (erase tacGen₁)
