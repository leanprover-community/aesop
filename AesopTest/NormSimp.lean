/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- A basic test for local simp rules.
example {α : Prop} (h : α) : α := by
  aesop (rule_sets [-builtin,-default]) (add h norm simp)

-- This test checks that we don't 'self-simplify' hypotheses: `h` should not
-- be used to simplify itself.
example (h : (α ∧ β) ∨ γ) : α ∨ γ := by
  aesop (add h norm simp)

-- Ditto, but we can omit the 'norm'.
example (h : (α ∧ β) ∨ γ) : α ∨ γ := by
  aesop (add h simp)

-- This test checks that the norm simp config is passed around properly.
example {α β : Prop} (ha : α) (h : α → β) : β := by
  fail_if_success aesop (rule_sets [-builtin,-default])
    (simp_options := { maxDischargeDepth := 0 })
    (options := { terminal := true })
  aesop (rule_sets [-builtin,-default])

-- We can use the `useHyps` config option to switch between `simp_all` and
-- `simp at *`.
example {α : Prop} (ha : α) : α := by
  fail_if_success aesop (rule_sets [-builtin,-default])
    (simp_options := { useHyps := false })
    (options := { terminal := true })
  aesop (rule_sets [-builtin,-default])

-- We can give priorities to `simp` rules, corresponding to the priorities of
-- `simp` lemmas.

opaque T : Prop

@[aesop simp 1]
axiom TF : T ↔ False

@[aesop simp 2]
axiom TT : T ↔ True

example : T := by aesop

attribute [-aesop] TF
attribute [aesop simp 3] TF

example : T := by
  fail_if_success aesop (options := { terminal := true })
  rw [TT]; trivial
