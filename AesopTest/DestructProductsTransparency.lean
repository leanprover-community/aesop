/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop safe constructors]
structure Sig (α : Sort u) (β : α → Sort v) : Sort _ where
  fst : α
  snd : β fst

def T α β := α ∧ β

example (h : T α β) : Sig α (λ _ => β) := by
  fail_if_success aesop (options := { terminal := true })
  aesop (options := { destructProductsTransparency := .default })

def U := T

example (h : U α β) : Sig α (λ _ => β) := by
  fail_if_success aesop (options := { terminal := true })
  aesop (options := { destructProductsTransparency := .default })

example (h : U α β ∧ U γ δ) : Sig α (λ _ => γ) := by
  fail_if_success aesop (options := { terminal := true })
  aesop (options := { destructProductsTransparency := .default })
