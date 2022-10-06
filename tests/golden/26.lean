/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

attribute [-simp] List.all_cons List.all_nil List.all_eq_true

theorem all_cons (P : α → Bool) (x : α) (xs : List α) (h : (x :: xs).all P)
  : P x ∧ xs.all P := by
  aesop
