/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

macro "aesop!" : tactic =>
  `(tactic| aesop (config := { warnOnNonterminal := false }))

axiom falso : ∀ {α : Sort _}, α

macro "falso" : tactic => `(tactic| exact falso)

@[aesop norm -100 forward (pattern := (↑n : Int))]
axiom nat_pos (n : Nat) : 0 ≤ (↑n : Int)

example (m n : Nat) : (↑m : Int) < 0 ∧ (↑n : Int) > 0 := by
  set_option aesop.check.script.steps false in -- TODO lean4#4315
  set_option aesop.check.script false in
  aesop!
  all_goals
    guard_hyp fwd_1 : 0 ≤ (m : Int)
    guard_hyp fwd_2 : 0 ≤ (n : Int)
    falso

@[aesop safe forward (pattern := min x y)]
axiom foo : ∀ {x y : Nat} (_ : 0 < x) (_ : 0 < y), 0 < min x y

example (hx : 0 < x) (hy : 0 < y) (_ : min x y < z): False := by
  aesop!
  guard_hyp fwd : 0 < min x y
  falso

axiom abs (n : Int) : Nat

notation "|" t "|" => abs t

@[aesop safe forward (pattern := |a + b|)]
axiom triangle (a b : Int) : |a + b| ≤ |a| + |b|

example : |a + b| ≤ |c + d| := by
  aesop!
  guard_hyp fwd   : |c + d| ≤ |c| + |d|
  guard_hyp fwd_1 : |a + b| ≤ |a| + |b|
  falso

@[aesop safe apply (pattern := (0 : Nat))]
axiom falso' : True → False

/--
error: tactic 'aesop' failed, made no progress
Initial goal:
  ⊢ False
-/
#guard_msgs in
example : False := by
  aesop

example (h : n = 0) : False := by
  aesop (rule_sets := [-builtin])

-- Patterns may only contain variables mentioned in the rule.

/--
error: unknown identifier 'z'
-/
#guard_msgs in
@[aesop safe forward (pattern := z)]
axiom quuz (x y : Nat) : True

-- When a premise of a forward rule is mentioned in a pattern, it can't also
-- be an immediate argument.

@[aesop safe forward (pattern := (↑x : Int)) (immediate := [y])]
axiom bar (x y : Nat) : True

/--
error: aesop: forward builder: argument 'x' cannot be immediate since it is already determined by a pattern
-/
#guard_msgs in
@[aesop safe forward (pattern := (↑x : Int)) (immediate := [y, x])]
axiom baz (x y : Nat) : True

-- For types with 'reducibly hidden' forall binders, the pattern can only refer
-- to the syntactically visible variables.

abbrev T := (tt : True) → False

/--
error: unknown identifier 'tt'
-/
#guard_msgs in
@[aesop safe forward (pattern := tt)]
axiom falso₁ : T

-- We support dependencies in patterns. E.g. in the following pattern, only the
-- premise `x` occurs syntactically, but the type of `x` depends on `a` and `p`,
-- so these premises are also determined by the pattern instantiation.
-- (Thanks to Son Ho for this test case.)

@[aesop safe forward (pattern := x)]
theorem get_prop {a : Type} {p : a → Prop} (x : Subtype p) : p x.val :=
  x.property

example {a : Type} {p : a → Prop} (x : Subtype p × Subtype p)
    (h : x.1.val = x.2.val) : p x.1.val ∧ p x.2.val := by
  saturate
  apply And.intro <;> assumption
