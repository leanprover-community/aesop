/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

open Lean
open Lean.Meta
open Lean.Elab.Tactic

section EvenOdd

inductive Even : Nat → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

inductive Odd : Nat → Prop
| one : Odd 1
| plus_two {n} : Odd n → Odd (n + 2)

inductive EvenOrOdd : Nat → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

attribute [aesop unsafe] EvenOrOdd.even EvenOrOdd.odd
attribute [aesop safe] Even.zero Even.plus_two
attribute [aesop 100%] Odd.one Odd.plus_two

@[aesop norm unfold]
def EvenOrOdd' (n : Nat) : Prop := EvenOrOdd n

example : EvenOrOdd' 3 := by
  aesop

end EvenOdd

-- In this example, the goal is solved already during normalisation.
example : 0 = 0 := by aesop


-- An intentionally looping Aesop call, to test the limiting options
section Loop

structure Wrap (α) where
  unwrap : α

example (h : α → α) (h' : Wrap α) : α := by
  -- TODO check that Aesop reports the correct error, to eliminate false positives
  fail_if_success aesop (add safe h) (options := { maxRuleApplications := 20, maxGoals := 0, maxRuleApplicationDepth := 0 })
  fail_if_success aesop (add safe h) (options := { maxGoals := 20, maxRuleApplications := 0, maxRuleApplicationDepth := 0 })
  fail_if_success aesop (add safe h) (options := { maxRuleApplicationDepth := 20, maxGoals := 0, maxRuleApplications := 0 })
  exact h'.unwrap

end Loop


-- This example tests the builtin rule that applies local hypotheses.
example (Even : Nat → Prop) (zero : Even 0)
    (plusTwo : ∀ n, Even n → Even (n + 2)) : Even 20 := by
  aesop
