/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

attribute [aesop unsafe 50% constructors] List.Mem

@[aesop safe [constructors, (cases (patterns := [All _ [], All _ (_ :: _)]))]]
inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more (x xs) : P x → All P xs → All P (x :: xs)

theorem weaken (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α) (h : All P xs)
  : All Q xs := by
  induction h <;> aesop

theorem in_self (xs : List α) : All (· ∈ xs) xs := by
  induction xs
  case nil =>
    aesop
  case cons x xs ih =>
    have wk : ∀ a, a ∈ xs → a ∈ x :: xs := by aesop
    have ih' : All (fun a => a ∈ x :: xs) xs := by aesop (add unsafe 1% weaken)
    aesop
