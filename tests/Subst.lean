/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

-- These test cases test the builtin subst tactic.

example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  aesop

example (h₁ : x = y) (h₂ : y = z) : x = z := by
  aesop

example (P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) : x = y := by
  aesop
