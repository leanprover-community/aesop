/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- Thanks to Bruno Dutertre for reporting this bug.

import Aesop

axiom R {α} : α → α → Prop

@[aesop safe forward] axiom sym : R x y → R y x
@[aesop safe forward] axiom tran : R x y → R y z → R x z

/--
info: Try this:
  have fwd : R b y := sym h₃
  have fwd_1 : R a x := sym h₂
  have fwd_2 : R b b := tran (y := y) fwd h₃
  have fwd_3 : R y y := tran (y := b) h₃ fwd
  have fwd_4 : R a a := tran (y := x) fwd_1 h₂
  have fwd_5 : R x x := tran (y := a) h₂ fwd_1
  sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (α : Type u_1) (x y a b : α) (h₂ : R x a) (h₃ : R y b) : False := by
  aesop? (rule_sets := [-builtin]) (config := { warnOnNonterminal := false })
  sorry
