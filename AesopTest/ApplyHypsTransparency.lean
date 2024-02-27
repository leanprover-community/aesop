/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def T := Unit → Nat

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Nat := by
  aesop (config := { applyHypsTransparency := .reducible, terminal := true })

example (h : T) : Nat := by
  aesop

@[irreducible] def U := Empty

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  aesop (config := { applyHypsTransparency := .reducible, terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  aesop (config := { terminal := true })

example (h : Unit → Empty) : U := by
  aesop (config := { applyHypsTransparency := .all })
