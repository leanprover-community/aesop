/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

attribute [aesop safe (cases (patterns := [List.Mem _ []]))] List.Mem
attribute [aesop unsafe 50% (cases (patterns := [List.Mem _ (_ :: _)]))] List.Mem

theorem Mem.split [DecidableEq α] (xs : List α) (v : α) (h : v ∈ xs)
  : ∃ l r, xs = l ++ v :: r := by
  induction xs
  case nil =>
    aesop
  case cons x xs ih =>
    have dec : Decidable (x = v) := inferInstance
    cases dec
    case isFalse no =>
      aesop (options := { terminal := true })
    case isTrue yes =>
      apply Exists.intro []
      apply Exists.intro xs
      rw [yes]
      rfl
