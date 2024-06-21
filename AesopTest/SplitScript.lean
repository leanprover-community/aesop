/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

open Classical

inductive MyFalse : Prop

/--
info: Try this:
  split
  next h => sorry
  next h => sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {A B : Prop} : if P then A else B := by
  aesop? (config := { warnOnNonterminal := false })
  all_goals sorry

/--
info: Try this:
  split at h
  next h_1 => simp_all only [true_or]
  next h_1 => simp_all only [or_true]
-/
#guard_msgs in
example (h : if P then A else B) : A ∨ B := by
  aesop?

/--
info: Try this:
  split at h
  next n => simp_all only [true_or]
  next n => simp_all only [true_or, or_true]
  next n_1 x x_1 => simp_all only [imp_false, or_true]
-/
#guard_msgs in
theorem foo (n : Nat) (h : match n with | 0 => A | 1 => B | _ => C) :
    A ∨ B ∨ C := by
  set_option aesop.check.rules false in -- TODO simp introduces mvar
  set_option aesop.check.tree false in
  aesop?
