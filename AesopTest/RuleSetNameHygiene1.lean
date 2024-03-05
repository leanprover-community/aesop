/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.RuleSetNameHygiene0

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

macro "aesop_test" : tactic => `(tactic| aesop (rule_sets := [test]))

@[aesop safe (rule_sets := [test])]
structure TT where

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : TT := by
  aesop (config := { terminal := true })

example : TT := by
  aesop_test
