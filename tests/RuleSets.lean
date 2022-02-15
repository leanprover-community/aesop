/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

declare_aesop_rule_sets [A, B, C, D]

@[aesop safe (rulesets [A])]
inductive A : Prop where
| intro

@[aesop safe (rulesets [B])]
inductive B : Prop where
| intro

@[aesop safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

example : A := by
  fail_if_success aesop
  aesop (rulesets [A])

example : B := by
  aesop (rulesets [A, B])

example : C := by
  fail_if_success aesop (rulesets [-default])
  aesop

attribute [aesop safe (rulesets [C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-aesop] C

example : C := by
  fail_if_success aesop (rulesets [C])
  aesop (safe [C])

@[aesop norm (builder simp)]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  aesop (rulesets [A])

attribute [-aesop] ad

example : D := by
  fail_if_success aesop (rulesets [A])
  aesop (norm [ad]) (rulesets [A])
