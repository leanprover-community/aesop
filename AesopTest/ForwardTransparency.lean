/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- Forward rules always operate at reducible transparency.

def T := Unit → Empty

variable {α : Type}

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : Unit) : α := by
  aesop (config := { terminal := true })

def U := Unit

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  aesop (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  aesop (add forward safe h) (config := { terminal := true })

abbrev V := Unit

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) (u : V) : α := by
  aesop (config := { terminal := true })

example (h : Unit → Empty) (u : V) : α := by
  aesop (add forward safe h)
