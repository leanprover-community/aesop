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
    (add safe [Even.zero, Even.plus_two, Odd.one, Odd.plus_two],
         unsafe [apply 50% EvenOrOdd.even, 50% EvenOrOdd.odd])

-- Same with local hypotheses, or a mix.
example : EvenOrOdd 3 := by
  have h : ∀ n, Odd n → EvenOrOdd n := λ _ p => EvenOrOdd.odd p
  aesop
    (add safe [Odd.one, Odd.plus_two], unsafe [EvenOrOdd.even 50%, h 50%])
    (erase Aesop.BuiltinRules.applyHyps) -- This rule subsumes h.

attribute [aesop 50%] Even.zero Even.plus_two

-- We can also erase global rules...
example : EvenOrOdd 2 := by
  fail_if_success aesop (add safe EvenOrOdd.even) (erase Even.zero)
    (options := { terminal := true })
  aesop (add safe EvenOrOdd.even)

-- ... as well as local ones (but what for?).
example : EvenOrOdd 2 := by
  have h : ∀ n, Even n → EvenOrOdd n := λ _ p => EvenOrOdd.even p
  fail_if_success
    aesop (add safe h) (erase Aesop.BuiltinRules.applyHyps, h)
      (options := { terminal := true })
  aesop (add safe h) (erase Aesop.BuiltinRules.applyHyps)
