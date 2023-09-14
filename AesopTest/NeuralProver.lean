import Aesop
-- import LeanInfer 
-- When we can use LeanInfer without importing it, this means the 
-- LeanInfer module successfully got integrated into the aesop dependency graph.

set_option aesop.check.all true

open Lean Lean.Meta Lean.Elab.Tactic

section simpleTest

structure neuralConfig where
  model_name : String

@[aesop unsafe neural]
def conf : neuralConfig := { model_name := "onnx-leandojo-lean4-tacgen-byt5-small" }

theorem foo (a: Nat) : a + 1 = Nat.succ a := by
  aesop
  -- aesop alone should be able to prove this simple theorem.

  -- suggest_tactics
  -- aesop should also be able to call LeanInfer to suggest tactics as LeanInfer is already added into the loop.
  
  -- rfl
  -- sorry
  -- both closes the proof each in a safe/unsafe way.