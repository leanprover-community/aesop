/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

attribute [aesop safe (cases (patterns := [List.Mem _ []]))] List.Mem
attribute [aesop unsafe 50% constructors] List.Mem
attribute [aesop unsafe 50% (cases (patterns := [List.Mem _ (_ :: _)]))] List.Mem

@[aesop safe [constructors, (cases (patterns := [All _ [], All _ (_ :: _)]))]]
inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more {x xs} : P x → All P xs → All P (x :: xs)

@[simp]
theorem All.cons (P : α → Prop) (x : α) (xs : List α)
  : All P (x :: xs) ↔ (P x ∧ All P xs) := by
  aesop

theorem mem (P : α → Prop) (xs : List α)
  : All P xs ↔ ∀ a : α, a ∈ xs → P a := by
  induction xs
  case nil => aesop
  case cons x xs ih => aesop (simp_options := { useHyps := false })
