/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

@[aesop safe]
axiom loopy {α : Prop} : α ∨ α → α

/--
warning: aesop: failed to prove the goal. Some goals were not explored because the maximum rule application depth (30) was reached. Set option 'maxRuleApplicationDepth' to increase the limit.
---
warning: aesop: safe prefix was not fully expanded because the maximum number of rule applications (50) was reached.
---
error: unsolved goals
case a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a
⊢ False
-/
#guard_msgs in
example : False := by
  aesop

/--
error: tactic 'aesop' failed, failed to prove the goal. Some goals were not explored because the maximum rule application depth (30) was reached. Set option 'maxRuleApplicationDepth' to increase the limit.
Initial goal:
  ⊢ False
Remaining goals after safe rules:
  case a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a.a
  ⊢ False
The safe prefix was not fully expanded because the maximum number of rule applications (50) was reached.
-/
#guard_msgs in
example : False := by
  aesop (config := { terminal := true })
