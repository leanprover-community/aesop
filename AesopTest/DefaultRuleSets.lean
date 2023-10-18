/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.DefaultRuleSetsInit

set_option aesop.check.all true

@[aesop norm unfold (rule_sets [regular₁])]
def T := True

example : T := by
  fail_if_success aesop (options := { terminal := true })
  aesop (rule_sets [regular₁])

@[aesop norm unfold (rule_sets [regular₂, dflt₁])]
def U := True

example : U := by
  fail_if_success aesop (rule_sets [-dflt₁]) (options := { terminal := true })
  aesop
