/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := Empty

example (h : T) : Empty := by
  fail_if_success
    aesop (erase Aesop.BuiltinRules.applyHyps)
      (options := { assumptionTransparency := .reducible, terminal := true })
  aesop (erase Aesop.BuiltinRules.applyHyps)

@[irreducible] def U := False

example (h : U) : False := by
  fail_if_success
    aesop (options := { terminal := true })
  aesop (options := { assumptionTransparency := .all })
