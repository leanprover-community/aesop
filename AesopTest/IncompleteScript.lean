/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- set_option aesop.check.script.steps false

/--
info: Try this:
  intro a
  simp_all only [Nat.add_zero]
  sorry
---
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
n : Nat
P : Nat → Prop
a : P n
⊢ P (n + 1)
-/
#guard_msgs in
example {P : Nat → Prop} : P (n + 0) → P (n + 1) := by
  aesop?

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

/--
info: Try this:
sorry
---
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : Even 5 := by
  aesop?

attribute [aesop safe constructors] Even

/--
info: Try this:
  apply Even.add_two
  apply Even.add_two
  sorry
---
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case a.a
⊢ Even 1
-/
#guard_msgs in
example : Even 5 := by
  aesop?
