/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.DefaultRuleSetsInit

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

@[aesop norm unfold (rule_sets := [regular₁])]
def T := True

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  aesop (config := { terminal := true })

example : T := by
  aesop (rule_sets := [regular₁])

@[aesop norm unfold (rule_sets := [regular₂, dflt₁])]
def U := True

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  aesop (rule_sets := [-dflt₁]) (config := { terminal := true })

example : U := by
  aesop
