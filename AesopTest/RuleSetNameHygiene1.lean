/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.RuleSetNameHygiene0

set_option aesop.check.all true

macro "aesop_test" : tactic => `(tactic| aesop (rule_sets [test]))

@[aesop safe (rule_sets [test])]
structure TT

example : TT := by
  fail_if_success aesop (options := { terminal := true })
  aesop_test
