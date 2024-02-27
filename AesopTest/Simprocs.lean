/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

open Lean Lean.Meta

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def unfoldConst («from» to : Name) : Simp.Simproc := λ e =>
  if e.isConstOf «from» then
    return .done { expr := .const to [] }
  else
    return .continue

@[irreducible] def T₁ := True

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : T₁ := by
  aesop

simproc unfoldT₁ (T₁) := unfoldConst ``T₁ ``True

example : T₁ := by
  aesop

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : T₁ := by
  aesop (config := { useDefaultSimpSet := false })

@[irreducible] def T₂ := True

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : T₂ := by
  aesop

simproc [aesop_builtin] unfoldT₂ (T₂) := unfoldConst ``T₂ ``True

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : T₂ := by
  aesop (rule_sets := [-builtin])

example : T₂ := by
  aesop
