/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

@[aesop [10% cases, safe constructors]]
inductive Even : Nat → Prop
  | zero : Even 0
  | plus_two : Even n → Even (n + 2)

example : Even 2 := by
  aesop

-- Removing the Aesop attribute erases all rules associated with the identifier
-- from all rule sets.
attribute [-aesop] Even

example : Even 2 := by
  fail_if_success aesop
  aesop (add safe Even)

-- We can also selectively remove rules in a certain phase or with a certain
-- builder.
attribute [aesop [unsafe 10% cases, safe constructors]] Even

erase_aesop_rules [ unsafe Even ]

example : Even 2 := by
  aesop

erase_aesop_rules [ constructors Even ]

example : Even 2 := by
  fail_if_success aesop
  aesop (add safe constructors Even)
