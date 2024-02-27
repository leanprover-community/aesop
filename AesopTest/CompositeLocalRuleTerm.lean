/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- Composite terms are supported by the `apply` and `forward` builders...

structure A where

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example (h : A → β → γ) (b : β) : γ := by
  aesop

example (h : A → β → γ) (b : β) : γ := by
  aesop (add safe apply (h {}))

example (h : A → β → γ) (b : β) : γ := by
  aesop (add safe forward (h {}))

-- ... and also by the `simp` builder.

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  aesop

example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  aesop (add simp (h {}))

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  aesop

example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  aesop (add simp [(h₁ {}), (h₂ {})])
