/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- TODO clean up this test case

import Aesop

set_option aesop.check.all true

inductive Even : Nat → Prop
| zero : Even Nat.zero
| plus_two {n} : Even n → Even (Nat.succ (Nat.succ n))

inductive Odd : Nat → Prop
| one : Odd (Nat.succ Nat.zero)
| plus_two {n} : Odd n → Odd (Nat.succ (Nat.succ n))

inductive EvenOrOdd : Nat → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

set_option pp.all false
sudo set_option trace.Aesop.RuleSet false
sudo set_option trace.Aesop.Steps false

-- We can add constants as rules.
example : EvenOrOdd 3 := by
  aesop
    (safe [Even.zero, Even.plus_two, Odd.one, Odd.plus_two])
    (unsafe [EvenOrOdd.even 50% (builder apply), EvenOrOdd.odd 50%])

-- Same with local hypotheses, or a mix.
example : EvenOrOdd 3 := by
  have h₂ : ∀ n, Odd n → EvenOrOdd n := λ _ p => EvenOrOdd.odd p
  aesop
    (safe [Odd.one, Odd.plus_two])
    (unsafe [EvenOrOdd.even 50%, h₂ 50%])
