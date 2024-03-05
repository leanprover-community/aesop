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
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : T := by
  aesop

@[aesop norm simp]
def F := False

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : F := by
  aesop

def F' := False

@[aesop safe apply]
theorem F'_def : False → F' := id

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : F' := by
  aesop

attribute [-aesop] F'_def
attribute [aesop 100%] F'_def

-- When an unsafe rule is applied, we don't count this as progress because the
-- remaining goal that the user gets to see is exactly the same as the initial
-- goal.

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : F' := by
  aesop
