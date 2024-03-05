/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

variable {α : Type}

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : α) : α := by
  aesop (rule_sets := [-builtin,-default])
        (add safe h apply (index := [target False]))
        (config := { terminal := true })

example (h : α) : α := by
  aesop (rule_sets := [-builtin,-default]) (add safe h apply)

-- See Com test for a more realistic scenario.
