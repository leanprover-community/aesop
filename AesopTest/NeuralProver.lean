import Aesop
-- import LeanInfer 
-- When we can use LeanInfer without importing it, this means the 
-- LeanInfer module successfully got integrated into the aesop dependency graph.

set_option aesop.check.all true

open Lean Lean.Meta Lean.Elab.Tactic

section simpleTest

theorem foo (a: Nat) : a + 1 = Nat.succ a := by
  aesop
  -- aesop (rule_sets [-default, -builtin])
  -- suggest_tactics
  -- rfl
  -- sorry