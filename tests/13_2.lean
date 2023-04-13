/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

inductive Perm : (xs ys : List α) → Type where
  | prep {xs} x : Perm (x :: xs) (x :: xs)

inductive Proof : (Γ Δ : List Φ) → Prop where
  | basic (Γ Δ n) : Proof (n :: Γ) (n :: Δ)
  | per_l (Γ Γ' Δ) : Proof Γ Δ → Perm Γ' Γ → Proof Γ' Δ

theorem weaken (Γ Δ : List Φ) (prf : Proof Γ Δ) (δ : Φ) : Proof Γ (δ :: Δ) := by
  induction prf
  case basic Γ Δ n =>
    aesop (add unsafe [constructors Proof, constructors Perm])
      (options := { maxRuleApplications := 50, terminal := true })
  case per_l Γ Γ' Δ _ perm ih =>
    apply Proof.per_l Γ Γ' (δ :: Δ) ih perm
