/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

structure MyTrue₁
structure MyTrue₂

@[aesop safe]
structure MyTrue₃ where
  tt : MyTrue₁

/--
warning: aesop: failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyTrue₃ := by
  aesop
  apply MyTrue₁.mk

@[aesop safe]
structure MyFalse where
  falso : False

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  aesop

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyFalse := by
  aesop (config := { terminal := true })

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  aesop (config := { warnOnNonterminal := false })

@[aesop safe]
structure MyFalse₂ where
  falso : False
  tt : MyTrue₃

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case falso
⊢ False

case tt
⊢ MyTrue₁
-/
#guard_msgs in
example : MyFalse₂ := by
  aesop
