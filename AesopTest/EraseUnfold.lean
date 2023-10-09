/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jannis Limperg
-/

-- Thanks to Jireh Loreaux for reporting this MWE.

import Aesop

set_option aesop.check.all true

@[irreducible]
def foo : Nat := 37

example : foo = 37 := by
  fail_if_success aesop (options := { terminal := true })
  unfold foo
  rfl

attribute [aesop norm unfold] foo

example : foo = 37 := by aesop

attribute [-aesop] foo

example : foo = 37 := by
  fail_if_success aesop? (options := { terminal := true })
  unfold foo
  rfl
