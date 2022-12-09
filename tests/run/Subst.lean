/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- These test cases test the builtin subst tactic.

example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  fail_if_success
    aesop
      (erase Aesop.BuiltinRules.subst)
      (simp_options := { useHyps := false })
      (options := { terminal := true })
  aesop (simp_options := { useHyps := false })

example (h₁ : x = y) (h₂ : y = z) : x = z := by
  fail_if_success
    aesop
      (erase Aesop.BuiltinRules.subst)
      (simp_options := { useHyps := false })
      (options := { terminal := true })
  aesop (simp_options := { useHyps := false })

example (P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) : x = y := by
  fail_if_success
    aesop
      (erase Aesop.BuiltinRules.subst,
             Aesop.BuiltinRules.assumption,
             Aesop.BuiltinRules.applyHyps)
      (simp_options := { useHyps := false })
      (options := { terminal := true })
  aesop
    (erase Aesop.BuiltinRules.assumption,
           Aesop.BuiltinRules.applyHyps)
    (simp_options := { useHyps := false })

-- Subst also works for bi-implications.
example (h₁ : P ↔ Q) (h₂ : Q ↔ R) (h₃ : P) : R  := by
  fail_if_success
    aesop
      (erase Aesop.BuiltinRules.subst)
      (simp_options := { useHyps := false })
      (options := { terminal := true })
  aesop (simp_options := { useHyps := false })

-- Subst also works for morally-homogeneous heterogeneous equalities (using a
-- builtin simp rule which turns these into actual homogeneous equalities).
example {P : α → Prop} {x y z : α} (h₁ : HEq x y) (h₂ : HEq y z) (h₃ : P x) :
    P z  := by
  fail_if_success
    aesop
      (erase Aesop.BuiltinRules.subst)
      (simp_options := { useHyps := false })
      (options := { terminal := true })
  aesop (simp_options := { useHyps := false })
