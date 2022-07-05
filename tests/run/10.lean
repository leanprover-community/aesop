/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

attribute [aesop unsafe [50% constructors, 50% cases]] List.Mem

theorem Mem.map (f : α → β) (x : α) (xs : List α) (h : x ∈ xs) :
    f x ∈ xs.map f := by
  induction h
  case tail =>
    aesop
  case head =>
    aesop
