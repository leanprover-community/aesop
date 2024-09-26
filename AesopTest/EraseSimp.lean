/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

example (n : Nat) : n + m = m + n := by
  aesop (add simp Nat.add_comm)

attribute [local simp] Nat.add_comm

example (n : Nat) : n + m = m + n := by
  aesop

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  aesop (erase Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  aesop (erase norm simp Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: aesop: 'Nat.add_comm' is not registered (with the given features) in any rule set.
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  aesop (erase apply Nat.add_comm)
