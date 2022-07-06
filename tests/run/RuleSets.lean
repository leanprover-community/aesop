/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

declare_aesop_rule_sets [A, B, C, D]

@[aesop safe (rule_sets [A])]
inductive A : Prop where
| intro

@[aesop safe (rule_sets [B])]
inductive B : Prop where
| intro

@[aesop safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

example : A := by
  fail_if_success aesop (options := { terminal := true })
  aesop (rule_sets [A])

example : B := by
  aesop (rule_sets [A, B])

example : C := by
  fail_if_success aesop (rule_sets [-default]) (options := { terminal := true })
  aesop

attribute [aesop safe (rule_sets [C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-aesop] C

example : C := by
  fail_if_success aesop (rule_sets [C]) (options := { terminal := true })
  aesop (add safe C)

@[aesop norm simp]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  aesop (rule_sets [A])

attribute [-aesop] ad

example : D := by
  fail_if_success aesop (rule_sets [A]) (options := { terminal := true })
  aesop (add norm ad) (rule_sets [A])
