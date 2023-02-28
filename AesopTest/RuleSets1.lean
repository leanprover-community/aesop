/-
Copyright (c) 2022-2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.RuleSets0

set_option aesop.check.all true

@[aesop safe (rule_sets [test_A])]
inductive A : Prop where
| intro

@[aesop safe (rule_sets [test_B])]
inductive B : Prop where
| intro

@[aesop safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

example : A := by
  fail_if_success aesop (options := { terminal := true })
  aesop (rule_sets [test_A])

example : B := by
  aesop (rule_sets [test_A, test_B])

example : C := by
  fail_if_success aesop (rule_sets [-default]) (options := { terminal := true })
  aesop

attribute [aesop safe (rule_sets [test_C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-aesop] C

example : C := by
  fail_if_success aesop (rule_sets [test_C]) (options := { terminal := true })
  aesop (add safe C)

@[aesop norm simp]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  aesop (rule_sets [test_A])

attribute [-aesop] ad

example : D := by
  fail_if_success aesop (rule_sets [test_A]) (options := { terminal := true })
  aesop (add norm ad) (rule_sets [test_A])

-- Rules can also be local.

inductive E : Prop where
  | intro

section

attribute [local aesop safe] E

example : E := by
  aesop

end

example : E := by
  fail_if_success aesop (options := { terminal := true })
  constructor

-- Rules can also be scoped.

namespace EScope

attribute [scoped aesop safe] E

example : E := by
  aesop

end EScope

example : E := by
  fail_if_success aesop (options := { terminal := true })
  open EScope in aesop
