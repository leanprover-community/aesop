/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/
import Aesop

set_option aesop.check.all true

attribute [aesop unsafe [50% constructors, 50% cases]] List.Mem

theorem Mem.map (f : α → β) (x : α) (xs : List α) (h : x ∈ xs) :
    f x ∈ xs.map f := by
  induction h <;> aesop
