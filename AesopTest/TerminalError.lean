/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
Initial goal:
  ⊢ False
Remaining goals after safe rules:
  ⊢ False
-/
#guard_msgs in
example : False := by
  aesop (config := { terminal := true })
