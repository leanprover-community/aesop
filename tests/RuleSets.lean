/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

declare_aesop_rule_sets [A, B, C, D]

@[aesop safe (rulesets [A])]
inductive A where
| intro

@[aesop safe (rulesets [B])]
inductive B where
| intro

@[aesop safe]
inductive C where
| intro

example : A := by
  fail_if_success aesop
  aesop (rulesets [A])

example : B := by
  aesop (rulesets [A, B])

example : C := by
  fail_if_success aesop (rulesets [-default])
  aesop
