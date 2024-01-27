/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

@[aesop safe]
axiom loopy {α : Prop} : α ∨ α → α

example : false := by
  aesop
