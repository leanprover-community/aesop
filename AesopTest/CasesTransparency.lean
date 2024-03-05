/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

example (h : False) : α := by
  aesop

def T := False

variable {α : Type}

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  aesop (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  aesop (add safe cases (transparency! := reducible) False)
    (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  aesop (add safe cases (transparency := default) False)
    (config := { terminal := true })

example (h : T) : α := by
  aesop (add safe cases (transparency! := default) False)

def U := T

example (h : U) : α := by
  aesop (add safe cases (transparency! := default) False)
