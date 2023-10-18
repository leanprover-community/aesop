/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

structure MyTrue₁
structure MyTrue₂

@[aesop safe]
structure MyTrue₃ where
  tt : MyTrue₁

example : MyTrue₃ := by
  aesop
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
  tt : MyTrue₃

example : MyFalse₂ := by
  aesop
