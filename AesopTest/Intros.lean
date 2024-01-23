/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def Injective₁ (f : α → β) := ∀ x y, f x = f y → x = y

abbrev Injective₂ (f : α → β) := ∀ x y, f x = f y → x = y

example : Injective₁ (@id Nat) := by
  fail_if_success aesop (config := { terminal := true })
  fail_if_success aesop (config := { introsTransparency? := some .reducible, terminal := true })
  aesop (config := { introsTransparency? := some .default })

example : Injective₂ (@id Nat) := by
  fail_if_success aesop (config := { terminal := true })
  aesop (config := { introsTransparency? := some .reducible })

example : Injective₂ (@id Nat) := by
  aesop (config := { introsTransparency? := some .default })
