/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

attribute [aesop safe] Exists.intro Sigma.mk
-- TODO these should be default rules

example (P : α → Prop) (a : α) (h : P a) : ∃ a, P a := by
  aesop

example (P : α → β → Prop) (a : α) (b : β) (h : P a b) : ∃ a b, P a b := by
  aesop

example (P : α → Type) (a : α) (h : P a) : Σ a, P a := by
  aesop

example (P : α → β → Type) (a : α) (b : β) (h : P a b) : Σ a b, P a b := by
  aesop

example (P Q : α → Prop) (hPQ : ∀ a, P a → Q a) (a : α) (h : P a) : ∃ a, Q a := by
  aesop

example (P Q Dead R : α → Prop)
    (hPQ : ∀ a, P a → Q a)
    (hDeadR : ∀ a, Dead a → R a)
    (hQR : ∀ a, Q a → R a)
    (a : α) (h : P a) :
    ∃ a, R a := by
  aesop

example (R : α → α → Prop) (R_trans : ∀ x y z, R x y → R y z → R x z) (a b c d)
    (hab : R a b) (hbc : R b c) (hcd : R c d) : R a d := by
  aesop
