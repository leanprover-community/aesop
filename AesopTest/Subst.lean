/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- These test cases test the builtin subst tactic.

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  aesop (erase Aesop.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  aesop (config := { useSimpAll := false })

variable {α : Type}

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z := by
  aesop (erase Aesop.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z := by
  aesop (config := { useSimpAll := false })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {x y : α }(P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) :
    x = y := by
  aesop
    (erase Aesop.BuiltinRules.subst, Aesop.BuiltinRules.assumption,
           Aesop.BuiltinRules.applyHyps)
    (config := { useSimpAll := false, terminal := true })

example {x y : α }(P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) :
    x = y := by
  aesop
    (erase Aesop.BuiltinRules.assumption,
           Aesop.BuiltinRules.applyHyps)
    (config := { useSimpAll := false })

-- Subst also works for bi-implications.

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h₁ : P ↔ Q) (h₂ : Q ↔ R) (h₃ : P) : R  := by
  aesop (erase Aesop.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example (h₁ : P ↔ Q) (h₂ : Q ↔ R) (h₃ : P) : R  := by
  aesop (config := { useSimpAll := false })

-- Subst also works for morally-homogeneous heterogeneous equalities (using a
-- builtin simp rule which turns these into actual homogeneous equalities).

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {P : α → Prop} {x y z : α} (h₁ : HEq x y) (h₂ : HEq y z) (h₃ : P x) :
    P z  := by
  aesop (erase Aesop.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example {P : α → Prop} {x y z : α} (h₁ : HEq x y) (h₂ : HEq y z) (h₃ : P x) :
    P z  := by
  aesop (config := { useSimpAll := false })
