/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop

set_option aesop.check.all true

@[aesop 50% cases]
inductive FancyAnd (α β : Prop) : Prop
| dummy (p : Empty)
| and (a : α) (b : β)

attribute [aesop safe -51 cases] Empty

example {α β} (h : FancyAnd α β) : α ∧ β := by
  aesop
