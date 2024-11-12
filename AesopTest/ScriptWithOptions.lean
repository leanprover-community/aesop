/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- FIXME: the tombstone in the "try this" suggestion below appeared in nightly-2024-11-03,
-- presumably because of https://github.com/leanprover/lean4/pull/5898
/--
info: Try this:
simp_all (config✝ := { }) only
-/
#guard_msgs in
example : True := by
  aesop? (config := {}) (simp_config := {})
