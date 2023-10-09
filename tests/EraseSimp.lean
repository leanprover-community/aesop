/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example (n : Nat) : n + m = m + n := by
  aesop (add simp Nat.add_comm)

attribute [local simp] Nat.add_comm

example (n : Nat) : n + m = m + n := by
  aesop

example (n : Nat) : n + m = m + n := by
  aesop (erase Nat.add_comm) (options := { warnOnNonterminal := false })
  aesop

example (n : Nat) : n + m = m + n := by
  aesop (erase norm simp Nat.add_comm) (options := { warnOnNonterminal := false })
  aesop

example (n : Nat) : n + m = m + n := by
  aesop (erase apply Nat.add_comm)
  aesop
