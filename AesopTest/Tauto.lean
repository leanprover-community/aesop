/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- This is an example which is currently challenging for Lean 4 `tauto`.
example {α : Type} [LE α] (a b c : α) (x₀ x₁ x₂ : Prop)
 (this1 : x₀ → x₁ → a ≤ c)
 (this2 : x₁ → x₂ → b ≤ a)
 (this3 : x₂ → x₀ → c ≤ b) :
    ((x₀ ∧ ¬b ≤ a) ∧ x₁ ∧ ¬c ≤ b ∨
         (x₁ ∧ ¬c ≤ b) ∧ x₂ ∧ ¬a ≤ c ∨ (x₂ ∧ ¬a ≤ c) ∧ x₀ ∧ ¬b ≤ a ↔
       (x₀ ∧ x₁ ∨ x₁ ∧ x₂ ∨ x₂ ∧ x₀) ∧
         ¬(c ≤ b ∧ b ≤ a ∨ b ≤ a ∧ a ≤ c ∨ a ≤ c ∧ c ≤ b)) :=
by aesop
