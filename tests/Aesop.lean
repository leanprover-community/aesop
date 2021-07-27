/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- TODO clean up this test case
import Lean
import Aesop.Main

open Lean
open Lean.Meta
open Lean.Elab.Tactic

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

set_option pp.all false
sudo set_option trace.Aesop.RuleSet false
sudo set_option trace.Aesop.Steps false

example : EvenOrOdd' 3 := by aesop

-- In this example, the goal is solved already during normalisation.
example : 0 = 0 := by aesop
