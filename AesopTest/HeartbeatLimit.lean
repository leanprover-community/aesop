/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop safe constructors]
inductive Even : Nat → Prop
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

example : Even 10 := by
  fail_if_success
    aesop (options := { maxRuleHeartbeats := 1, terminal := true })
  aesop

example (n m k : Nat) : n + m + k = (n + m) + k := by
  fail_if_success
    aesop (options := { maxSimpHeartbeats := 1, terminal := true })
  aesop
