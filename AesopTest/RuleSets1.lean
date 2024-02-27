/-
Copyright (c) 2022-2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.RuleSets0

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

@[aesop safe (rule_sets := [test_A])]
inductive A : Prop where
| intro

@[aesop safe (rule_sets := [test_B])]
inductive B : Prop where
| intro

@[aesop safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : A := by
  aesop (config := { terminal := true })

example : A := by
  aesop (rule_sets := [test_A])

example : B := by
  aesop (rule_sets := [test_A, test_B])

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  aesop (rule_sets := [-default]) (config := { terminal := true })

example : C := by
  aesop

attribute [aesop safe (rule_sets := [test_C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-aesop] C

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  aesop (rule_sets := [test_C]) (config := { terminal := true })

example : C := by
  aesop (add safe C)

@[aesop norm simp]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  aesop (rule_sets := [test_A])

attribute [-aesop] ad

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : D := by
  aesop (rule_sets := [test_A]) (config := { terminal := true })

example : D := by
  aesop (add norm ad) (rule_sets := [test_A])

-- Rules can also be local.

inductive E : Prop where
  | intro

section

attribute [local aesop safe] E

example : E := by
  aesop

end

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  aesop (config := { terminal := true })

example : E := by
  constructor

-- Rules can also be scoped.

namespace EScope

attribute [scoped aesop safe] E

example : E := by
  aesop

end EScope

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  aesop (config := { terminal := true })

example : E := by
  open EScope in aesop
