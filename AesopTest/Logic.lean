/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example : True := by
  aesop

example : Unit := by
  aesop

example : PUnit.{u} := by
  aesop

example (h : False) : α := by
  aesop

example (h : Empty) : α := by
  aesop

example (h : PEmpty.{u}) : α := by
  aesop
