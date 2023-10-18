/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example {n m k : Nat} (h : n < m) (h₂ : m < k) : n < k := by
  apply Nat.lt_trans <;> aesop
