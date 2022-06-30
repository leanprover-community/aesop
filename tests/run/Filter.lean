/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

namespace TBA

inductive List (α : Type) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

notation  (priority := high) "[" "]" => List.nil
infixr:67 (priority := high) " :: "  => List.cons

def filter (p : α → Prop) [DecidablePred p] (as : List α) : List α :=
  match as with
  | [] => []
  | a::as => if p a then a :: filter p as else filter p as

variable {p : α → Prop} [DecidablePred p] {as bs : List α}

@[simp]
theorem filter_cons_true (h : p a) : filter p (a :: as) = a :: filter p as := by
  simp [filter, h]

@[simp]
theorem filter_cons_false (h : ¬ p a) : filter p (a :: as) = filter p as := by
  simp [filter, h]

@[aesop 50% [constructors, cases]]
inductive Mem (a : α) : List α → Prop where
  | head {as} : Mem a (a::as)
  | tail {as} : Mem a as → Mem a (a'::as)

infix:50 " ∈ " => Mem

theorem mem_filter : a ∈ filter p as ↔ a ∈ as ∧ p a := by
  apply Iff.intro
  case mp =>
    intro h
    induction as with
    | nil => cases h
    | cons a' as ih => by_cases ha' : p a' <;> aesop
  case mpr =>
    intro h
    induction as with
    | nil => cases h.1
    | cons a' as ih =>
      cases h.1 with
      | head =>
        rw [filter_cons_true h.2]
        constructor
      | tail ha =>
        have : a ∈ filter p as := ih ⟨ha, h.2⟩
        by_cases hpa' : p a'
        case inl =>
          rw [filter_cons_true hpa']
          exact Mem.tail this
        case inr =>
          rw [filter_cons_false hpa']
          exact this

end TBA
