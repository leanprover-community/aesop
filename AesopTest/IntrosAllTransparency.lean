/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[irreducible] def T := False → True

example : T := by
  fail_if_success aesop (options := { terminal := true })
  aesop (options := { introsTransparency? := some .all })
