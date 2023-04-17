/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := Unit → Nat

example (h : T) : Nat := by
  fail_if_success
    aesop (options := { applyHypsTransparency := .reducible, terminal := true })
  aesop

@[irreducible] def U := Empty

example (h : Unit → Empty) : U := by
  fail_if_success
    aesop (options := { applyHypsTransparency := .reducible, terminal := true })
  fail_if_success
    aesop (options := { terminal := true })
  aesop (options := { applyHypsTransparency := .all })
