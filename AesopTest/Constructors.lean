/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

@[aesop safe]
inductive Even : Nat → Type
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

example : Even 6 := by
  aesop

attribute [-aesop] Even

def T n := Even n

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T 6 := by
  aesop (config := { terminal := true })

example : T 6 := by
  aesop (add safe constructors (transparency! := default) Even)
