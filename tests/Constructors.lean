/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

inductive Even : Nat → Type
| zero : Even 0
| plusTwo : Even n → Even (n + 2)

-- TODO currently broken
-- attribute [aesop safe] Even

example : Even 6 := by
  -- TODO currently broken
  -- aesop
  exact Even.plusTwo $ Even.plusTwo $ Even.plusTwo Even.zero
