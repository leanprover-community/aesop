/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true
set_option linter.unreachableTactic false

@[aesop safe constructors]
inductive Even : Nat → Prop
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

/-- error: tactic 'aesop' failed, failed to prove the goal after exhaustive search. -/
#guard_msgs in
example : Even 10 := by
  aesop (config := { maxRuleHeartbeats := 1, terminal := true })

example : Even 10 := by
  aesop

/--
error: aesop: error in norm simp: (deterministic) timeout at `simp`, maximum number of heartbeats (1) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (n m k : Nat) : n + m + k = (n + m) + k := by
  aesop (config := { maxSimpHeartbeats := 1, terminal := true })

example (n m k : Nat) : n + m + k = (n + m) + k := by
  aesop
