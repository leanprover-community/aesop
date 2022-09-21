/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop

set_option aesop.check.all true

example (h : α) : α := by
  fail_if_success
    aesop (rule_sets [-builtin,-default])
          (add safe h (apply (index := [target False])))
          (options := { terminal := true })
  aesop (rule_sets [-builtin,-default]) (add safe h apply)

-- See Com test for a more realistic scenario.
