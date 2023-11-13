/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

set_option trace.aesop.proof true

example : α := by
  aesop

@[aesop norm simp]
def F := False

example : F := by
  aesop
