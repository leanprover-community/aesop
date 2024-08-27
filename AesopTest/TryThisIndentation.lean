/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

/--
info: Try this:
  intro a_1 a_2
  simp_all only [ne_eq, List.mem_cons, or_self, not_false_eq_true]
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  aesop?

/--
info: Try this:
simp_all only [ne_eq, List.mem_cons, or_self, not_false_eq_true]
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  intros
  have : ¬ a ∈ y :: l := by
    aesop?
  exact this
