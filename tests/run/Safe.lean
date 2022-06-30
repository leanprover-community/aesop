/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop 50%]
inductive Even : Nat → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

structure Even' (n) where
  even : Even n

theorem even'_of_false : False → Even' n
| h => nomatch h

theorem even'_of_even' : Even' n → Even' n :=
  id

-- Once a safe rule is applied, the corresponding goal is marked as inactive
-- and never visited again.
example : Even' 2 := by
  fail_if_success aesop
    (add safe [even'_of_false 0, Even'.mk 1])
  fail_if_success aesop
    (add safe [even'_of_even'], unsafe [Even'.mk 100%])
    (options := { maxRuleApplications := 10 })
  aesop
    (add safe [even'_of_false 1, Even'.mk 0])
