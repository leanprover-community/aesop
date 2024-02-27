/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

inductive Perm : (xs ys : List α) → Type where
  | prep {xs} x : Perm (x :: xs) (x :: xs)

inductive Proof : (Γ Δ : List Φ) → Prop where
  | basic (Γ Δ n) : Proof (n :: Γ) (n :: Δ)
  | per_l (Γ Γ' Δ) : Proof Γ Δ → Perm Γ' Γ → Proof Γ' Δ

/--
error: tactic 'aesop' failed, maximum number of rule applications (50) reached. Set the 'maxRuleApplications' option to increase the limit.
-/
#guard_msgs in
theorem weaken (Γ Δ : List Φ) (prf : Proof Γ Δ) (δ : Φ) : Proof Γ (δ :: Δ) := by
  induction prf
  case basic Γ Δ n =>
    aesop (add unsafe [constructors Proof, constructors Perm])
      (config := { maxRuleApplications := 50, terminal := true })
  case per_l Γ Γ' Δ _ perm ih =>
    apply Proof.per_l Γ Γ' (δ :: Δ) ih perm
