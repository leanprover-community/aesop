/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- Tests the builtin split rules.

@[aesop norm unfold]
def id' (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => .succ n


-- First, the rule for splitting targets.
example : id' n = n := by
  aesop

-- Second, the rule for splitting hypotheses. We introduce a custom equality to
-- make sure that in the following example, Aesop doesn't just substitute the
-- hypothesis during norm simp.
inductive MyEq (x : α) : α → Prop
  | rfl : MyEq x x

@[aesop unsafe]
def MyEq.elim : MyEq x y → x = y
  | rfl => by rfl

example (h : MyEq n (id' m)) : n = m := by
  aesop
