/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

inductive Even : Nat → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

inductive Odd : Nat → Prop
| one : Odd 1
| plus_two {n} : Odd n → Odd (n + 2)

inductive EvenOrOdd : Nat → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

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
