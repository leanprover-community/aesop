/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  aesop

example (m n : Nat) : m * n = n * m := by
  aesop (add safe (by rw [Nat.mul_comm]))

example (m n : Nat) : m * n = n * m := by
  aesop (add safe tactic (by rw [Nat.mul_comm m n]))

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  aesop (add safe (by rw [Nat.mul_comm m m]))

example (m n : Nat) : m * n = n * m := by
  aesop (add safe (by apply Nat.mul_comm; done))
