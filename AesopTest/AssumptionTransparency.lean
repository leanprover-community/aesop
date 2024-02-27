/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def T := Empty

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Empty := by
  aesop (erase Aesop.BuiltinRules.applyHyps)
    (config := { assumptionTransparency := .reducible, terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Empty := by
  aesop (erase Aesop.BuiltinRules.applyHyps)
    (config := { assumptionTransparency := .reducible, terminal := true })

example (h : T) : Empty := by
  aesop (erase Aesop.BuiltinRules.applyHyps)

@[irreducible] def U := False

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : U) : False := by
  aesop (config := { terminal := true })

example (h : U) : False := by
  aesop (config := { assumptionTransparency := .all })
