/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

axiom A : Type
axiom idA : A
axiom comp : A → A → A

@[simp]
axiom comp_id : ∀ f, comp f idA = f

set_option linter.unusedVariables false in
example (w : ∀ h, comp f h = comp g h) : f = comp f idA := by
  aesop
