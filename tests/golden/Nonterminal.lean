/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

structure MyTrue₁
structure MyTrue₂

@[aesop safe]
structure MyTrue₃ where
  tt : MyTrue₁

example : MyTrue₃ := by
  aesop
  apply MyTrue₁.mk

@[aesop safe]
inductive MyTrue₄
  | intro₁ : MyTrue₁ → MyTrue₄
  | intro₂ : MyTrue₂ → MyTrue₄

example : MyTrue₄ := by
  aesop
  fail_if_success apply MyTrue₂.mk
  apply MyTrue₁.mk

@[aesop safe]
structure MyFalse where
  falso : False

example : MyFalse := by
  aesop

example : MyFalse := by
  fail_if_success aesop (options := { terminal := true })

example : MyFalse := by
  aesop (options := { warnOnNonterminal := false })

@[aesop safe]
structure MyFalse₂ where
  falso : False
  tt : MyTrue₄

example : MyFalse₂ := by
  aesop
