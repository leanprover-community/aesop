/-
Copyright (c) 2026 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- A parenthesised rule term can be followed directly by projections; the whole
-- expression does not need an extra pair of parentheses. See
-- https://github.com/leanprover-community/aesop/issues/233

example (n a : Nat) : a + n = n + a := by
  aesop (add apply safe [(Nat.add_comm n a).symm])

-- The previously required extra parentheses keep working.

example (n a : Nat) : a + n = n + a := by
  aesop (add apply safe [((Nat.add_comm n a).symm)])

-- Projections can be chained.

example (n a : Nat) : n + a = a + n := by
  aesop (add apply safe [(Nat.add_comm n a).symm.symm])

-- Projected composite terms also work with the `simp` builder.

example {P : Nat → Prop} (h : P (1 + 2)) : P (2 + 1) := by
  aesop (add safe simp [(Nat.add_comm 1 2).symm])

-- `aesop?` prints the rule in the new, unparenthesised form.

/--
info: Try this:

  [apply]   apply (Nat.add_comm n a).symm
-/
#guard_msgs in
example (n a : Nat) : a + n = n + a := by
  aesop? (add apply safe [(Nat.add_comm n a).symm])
