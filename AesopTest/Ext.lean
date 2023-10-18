/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.Ext

example (f g : α → β) (h : ∀ a, f a = g a) : f = g := by
  aesop

attribute [local ext] Prod

example (x y : α × β) (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  aesop
