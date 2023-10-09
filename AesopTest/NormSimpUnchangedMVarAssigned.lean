/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills, Jannis Limperg
-/

-- Thanks to Thomas Murrills for reporting this bug.

import Aesop

set_option aesop.check.all true

class Foo (α : Type u) where
  f : α → α
  p : True

class Bar (α : Type u) extends Foo α where
  eq : ∀ x : α, f x = f x

def bar : Bar Unit where
  f := fun _ => ()
  eq := by aesop
  p := ?x
