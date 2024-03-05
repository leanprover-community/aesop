/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def T := True

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  aesop (add safe apply True.intro) (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  aesop (add safe apply (transparency := default) True.intro)
    (config := { terminal := true })

example : T := by
  aesop (add safe apply (transparency! := default) True.intro)

@[irreducible] def U := T

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  aesop (add safe apply True.intro) (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  aesop (add safe apply (transparency := default) True.intro)
    (config := { terminal := true })

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  aesop (add safe apply (transparency! := default) True.intro)
    (config := { terminal := true })

example : U := by
  aesop (add safe apply (transparency! := all) True.intro)
