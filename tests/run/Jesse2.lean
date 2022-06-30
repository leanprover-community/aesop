/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- Thanks to Jesse Vogel for this test case. It demonstrates the handling of
-- 'dropped' mvars. A rapp drops an mvar if the mvar appears in the parent goal
-- of the rapp, but not in any of its subgoals. In this case, we add an
-- additional regular goal for the mvar.

import Aesop

set_option aesop.check.all true

axiom Ring : Type

axiom RingHom (R S : Ring) : Type

@[aesop 99%]
axiom RingId (R : Ring) : RingHom R R

@[aesop 99%]
axiom ZZ : Ring

example : ∃ (R : Ring) (f : RingHom R R), True := by
  aesop
