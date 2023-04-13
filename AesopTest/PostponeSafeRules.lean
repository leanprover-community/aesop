/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- This is a test case for postponed safe rules. When a safe rule assigns mvars,
-- it is not applied but instead postponed. Then we later try it again as an
-- unsafe rule.
--
-- It's hard to test this feature completely because we can't really tell from
-- the outside when a rule has been applied. But we can at least look at the
-- traces of the following test cases.

axiom T : Nat → Prop

@[aesop safe]
axiom t : T 0

example : ∃ (i : Nat), T i := by
  aesop


axiom U : Nat → Prop

@[aesop safe 0]
axiom u₁ : U 0

@[aesop safe 1]
axiom u₂ : U 1

example : ∃ i, U i ∧ i = 1 := by
  aesop
