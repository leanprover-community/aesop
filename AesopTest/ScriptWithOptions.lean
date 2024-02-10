/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.GuardMsgs

set_option aesop.check.all true

/--
info: Try this:
  simp_all only
-/
#guard_msgs in
example : True := by
  aesop? (config := {})
