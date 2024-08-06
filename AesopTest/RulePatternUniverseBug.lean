/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho, Jannis Limperg
-/

-- A regression test for an issue where universe mvars were not correctly
-- assigned during rule pattern matching. Thanks to Son Ho for reporting this
-- issue.

import Aesop.Frontend.Attribute
import Aesop.Frontend.Saturate

set_option aesop.check.all true

namespace List

@[simp]
def len (ls : List α) : Int :=
  match ls with
  | [] => 0
  | _ :: tl => 1 + len tl

@[aesop safe forward (pattern := len ls)]
theorem len_pos : 0 ≤ len (ls : List α) := by
  induction ls <;> simp [*]
  omega

def indexOpt (ls : List α) (i : Int) : Option α :=
  match ls with
  | [] => none
  | hd :: tl => if i = 0 then some hd else indexOpt tl (i - 1)

theorem indexOpt_bounds (ls : List α) (i : Int) :
    ls.indexOpt i = none ↔ i < 0 ∨ ls.len ≤ i := by
  match ls with
  | [] => simp [indexOpt]; omega
  | _ :: tl =>
    have := indexOpt_bounds tl (i - 1)
    if h : i = 0 then
      simp [indexOpt, *]
      saturate
      omega
    else
      simp [indexOpt, len, *]
      constructor <;> intro a <;> cases a
      . left
        saturate
        omega
      . right; omega
      . left; omega
      . right; omega
