/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

inductive Any (P : α → Prop) : List α → Prop where
  | here (x xs) : P x → Any P (x :: xs)

inductive Perm : (xs ys : List α) → Type where
  | refl xs : Perm xs xs
  | prep (x xs ys) : Perm xs ys → Perm (x :: xs) (x :: ys)

theorem Perm.any {xs ys : List α} (perm : Perm xs ys) (P : α → Prop)
  : Any P xs → Any P ys := by
  induction perm <;> aesop (add safe [constructors Any, cases Any])

theorem error (P : Nat → Prop) (Δ : List Nat) : Any P Δ := by
  aesop (add 50% [constructors Perm, constructors Any, Perm.any])
    (options := { maxRuleApplications := 100, terminal := true })
  sorry

theorem fine (P : α → Prop) (Δ : List α) : Any P Δ := by
  aesop (add unsafe [50% constructors Perm, 50% constructors Any, apply 50% Perm.any])
    (options := { maxRuleApplications := 10, terminal := true })
  sorry
