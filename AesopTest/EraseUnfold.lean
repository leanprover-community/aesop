/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jannis Limperg
-/

-- Thanks to Jireh Loreaux for reporting this MWE.

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

@[irreducible]
def foo : Nat := 37

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  aesop (config := { terminal := true }) (erase Aesop.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl

attribute [aesop norm unfold] foo

example : foo = 37 := by aesop (erase Aesop.BuiltinRules.rfl)

attribute [-aesop] foo

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  aesop (config := { terminal := true }) (erase Aesop.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl
