/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example : 1 = 2 → False := by
  fail_if_success
    aesop (simp_options := { enabled := false })
      (options := { terminal := true })
  aesop
