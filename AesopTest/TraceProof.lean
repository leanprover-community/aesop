/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

set_option trace.aesop.proof true

/--
error: tactic 'aesop' failed, made no progress
---
info: [aesop.proof] <no proof>
-/
#guard_msgs in
example : α := by
  aesop

@[aesop norm simp]
def F := False

set_option pp.mvars false in
/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
---
info: [aesop.proof] id ?_
-/
#guard_msgs in
example : F := by
  aesop
