/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

open Classical

inductive MyFalse : Prop

/--
info: Try this:
  split <;> [rename_i h; rename_i h]
  · sorry
  · sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {A B : Prop} : if P then A else B := by
  aesop? (config := { warnOnNonterminal := false })
  all_goals sorry
