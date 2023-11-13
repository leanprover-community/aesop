/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := True

example : T := by
  aesop

@[aesop norm simp]
def F := False

example : F := by
  aesop

def F' := False

@[aesop safe apply]
theorem F'_def : False → F' := id

example : F' := by
  aesop
