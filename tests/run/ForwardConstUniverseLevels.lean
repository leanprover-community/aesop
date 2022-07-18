/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

@[aesop safe elim]
axiom ne_and_not_mem_of_not_mem_cons {α} {a y : α} {l : List α} :
    a ∉ y::l → a ≠ y ∧ a ∉ l

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ≠ b := by
  aesop
