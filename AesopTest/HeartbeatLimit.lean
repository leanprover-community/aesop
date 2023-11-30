/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.GuardMsgs

set_option aesop.check.all true
set_option linter.unreachableTactic false

@[aesop safe constructors]
inductive Even : Nat → Prop
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

/--
error: (deterministic) timeout at 'whnf', maximum number of heartbeats (1) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
-/
#guard_msgs in
example : Even 10 := by
  aesop (options := { maxRuleHeartbeats := 1, terminal := true })

example : Even 10 := by
  aesop

example (n m k : Nat) : n + m + k = (n + m) + k := by
  fail_if_success
    aesop (options := { maxSimpHeartbeats := 1, terminal := true })
  aesop
