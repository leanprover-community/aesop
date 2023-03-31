/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- This file tests the builtin rules that destruct hypotheses with product-like
-- types.

import Aesop

set_option aesop.check.all true

@[aesop safe constructors]
inductive Ex (α : Sort u) (β : α → Prop) : Prop
  | intro (fst : α) (snd : β fst)

@[aesop safe constructors]
structure Sig (α : Sort u) (β : α → Sort v) : Sort _ where
  fst : α
  snd : β fst

example (h : α ∧ β) : Sig α (λ _ => β) := by
  aesop

example (h : α × β) : Sig α (λ _ => β) := by
  aesop

example (h : PProd α β) : Sig α (λ _ => β) := by
  aesop

example (h : MProd α β) : Sig α (λ _ => β) := by
  aesop

example {p : α → Prop} (h : ∃ a, p a) : Ex α p := by
  aesop

example {p : α → Prop} (h : { a // p a }) : Sig α p := by
  aesop

example {p : α → Type} (h : Σ a, p a) : Sig α p := by
  aesop

example {p : α → Type} (h : Σ' a, p a) : Sig α p := by
  aesop
