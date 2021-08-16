/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- TODO clean up this test case
import Lean
import Aesop

set_option aesop.check.all true

open Lean
open Lean.Meta
open Lean.Elab.Tactic

section EvenOdd

inductive Even : Nat → Prop
| zero : Even Nat.zero
| plus_two {n} : Even n → Even (Nat.succ (Nat.succ n))

inductive Odd : Nat → Prop
| one : Odd (Nat.succ Nat.zero)
| plus_two {n} : Odd n → Odd (Nat.succ (Nat.succ n))

inductive EvenOrOdd : Nat → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

attribute [aesop  50%] EvenOrOdd.even EvenOrOdd.odd
attribute [aesop safe] Even.zero Even.plus_two
attribute [aesop 100%] Odd.one Odd.plus_two

def EvenOrOdd' (n : Nat) : Prop := EvenOrOdd n

@[aesop norm (builder tactic)]
def testNormTactic : TacticM Unit := do
  evalTactic (← `(tactic|try simp only [EvenOrOdd']))

example : EvenOrOdd' 3 := by aesop

end EvenOdd

-- In this example, the goal is solved already during normalisation.
example : 0 = 0 := by aesop


-- An example involving transitivity. This tests our handling of metavariables.
section Transitivity

axiom A : Type
axiom R : A → A → Prop

@[aesop 20%]
axiom R_trans : ∀ x y z, R x y → R y z → R x z

@[aesop safe]
axiom R_refl : ∀ x, R x x

example {a b c d} (hab : R a b) (hbc : R b c) (hcd : R c d) : R a d := by
  aesop

end Transitivity


-- An intentionally looping Aesop call, to test the limiting options
section Loop

structure Wrap (α) where
  unwrap : α

example (h : α → α) (h' : Wrap α) : α := by
  failIfSuccess aesop (safe [h]) (options { maxRuleApplications := 20, maxGoals := 0, maxRuleApplicationDepth := 0 })
  failIfSuccess aesop (safe [h]) (options { maxGoals := 20, maxRuleApplications := 0, maxRuleApplicationDepth := 0 })
  failIfSuccess aesop (safe [h]) (options { maxRuleApplicationDepth := 20, maxGoals := 0, maxRuleApplications := 0 })
  exact h'.unwrap

end Loop
