/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def Involutive (f : α → α) : Prop :=
  ∀ x, f (f x) = x

example : Involutive not := by
  aesop (add norm simp Involutive)

example : Involutive not := by
  aesop (add norm unfold Involutive)
