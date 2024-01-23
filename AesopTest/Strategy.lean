/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop 50% constructors]
inductive I₁
  | ofI₁ : I₁ → I₁
  | ofTrue : True → I₁

example : I₁ := by
  aesop

example : I₁ := by
  aesop (config := { strategy := .bestFirst })

example : I₁ := by
  aesop (config := { strategy := .breadthFirst })

example : I₁ := by
  fail_if_success
    aesop (config :=
      { strategy := .depthFirst,
        maxRuleApplicationDepth := 0,
        maxRuleApplications := 10,
        terminal := true })
  aesop (config :=
    { strategy := .depthFirst,
      maxRuleApplicationDepth := 10 })
