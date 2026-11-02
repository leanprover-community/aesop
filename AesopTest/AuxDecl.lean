/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.BVDecide

/-
This test case checks whether tactics that make use of auxiliary declarations,
such as `omega` and `bv_decide`, work with Aesop. Auxiliary declarations are
problematic because we can't allows tactics on different branches of the search
tree to add auxiliary declarations with the same name.
-/

theorem foo (m n : Nat) : n + m = m + n ∧ m + n = n + m := by
  fail_if_success aesop (config := { terminal := true })
  aesop (add safe (by omega))

local instance [Add α] [Add β] : Add (α × β) :=
  ⟨λ (a, b) (a', b') => (a + a', b + b')⟩

theorem bar
    (fst snd fst_1 snd_1 fst_2 snd_2 w w_1 w_2 w_3 : BitVec 128)
    (left : w_1.uaddOverflow w_3 = true)
    (left_1 : w.uaddOverflow w_2 = true)
    (right : (w_1 + w_3).uaddOverflow 1#128 = true) :
    (fst_2, snd_2) = (fst, snd) + (fst_1, snd_1) := by
  aesop (add safe (by bv_decide))

theorem baz (a b : BitVec 1) : (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) := by
  aesop (add safe 1000 (by bv_decide))

/-
Rules applied to sibling goals run in states whose environments do not contain
each other's auxiliary declarations. Here `omega` closes the goals `4 < f 0` and
`4 < f 1`, as a safe rule and as a norm rule. It used to give both auxiliary
theorems the same name under synchronous elaboration, and the kernel then
rejected the extracted proof.
-/

set_option Elab.async false in
theorem qux (f : Nat → Nat) (a : Nat) (h : a = 0 ∨ a = 1) (h₀ : f 0 = 5)
    (h₁ : f 1 = 7) : 4 < f a := by
  aesop (add safe (by omega)) (config := { enableSimp := false })

set_option Elab.async false in
theorem quux (f : Nat → Nat) (a : Nat) (h : a = 0 ∨ a = 1) (h₀ : f 0 = 5)
    (h₁ : f 1 = 7) : 4 < f a := by
  aesop (add norm (by omega)) (config := { enableSimp := false })
