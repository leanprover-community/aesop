/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov, Jannis Limperg
-/

-- Test case for #284. Tests the handling of forward rule premises whose only
-- reverse dependencies are instances.
-- Thanks to Artie Khovanov for this test case.

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

class Base (S : Prop) : Prop where
  is_true : S

theorem foo [inst : Base S] : S :=
  inst.is_true

example [Base S] : S := by
  aesop (add safe forward foo)

class Extend S extends Base S

example [Extend S] : S := by
  aesop (add safe forward foo)
