/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- We used to add local rules to the `default` rule set, but this is doesn't
-- work well when the default rule set is disabled. Now we add local rules to
-- a separate `local` rule set.
example : Unit := by
  fail_if_success
    aesop (rule_sets [-default, -builtin])
  fail_if_success
    aesop (add safe PUnit.unit) (rule_sets [-default, -builtin, -«local»])
  aesop (add safe PUnit.unit) (rule_sets [-default, -builtin])
