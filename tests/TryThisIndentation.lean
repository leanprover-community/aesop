/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option trace.debug true

example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  aesop?

example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  intros
  have : ¬ a ∈ y :: l := by
    aesop?
  exact this