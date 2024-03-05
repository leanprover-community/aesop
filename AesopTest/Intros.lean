/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def Injective₁ (f : α → β) := ∀ x y, f x = f y → x = y

abbrev Injective₂ (f : α → β) := ∀ x y, f x = f y → x = y

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₁ (@id Nat) := by
  aesop (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₁ (@id Nat) := by
  aesop (config := { introsTransparency? := some .reducible, terminal := true })

example : Injective₁ (@id Nat) := by
  aesop (config := { introsTransparency? := some .default })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₂ (@id Nat) := by
  aesop (config := { terminal := true })

example : Injective₂ (@id Nat) := by
  aesop (config := { introsTransparency? := some .reducible })

example : Injective₂ (@id Nat) := by
  aesop (config := { introsTransparency? := some .default })
