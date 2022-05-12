/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example (h : α) : α := by
  fail_if_success aesop (rule_sets [-builtin,-default]) (add safe h (apply (index := [target False])))
  aesop                 (rule_sets [-builtin,-default]) (add safe h apply)

-- See Com test for a more realistic scenario.
