/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.GuardMsgs

set_option aesop.check.all true

macro "aesop!" : tactic =>
  `(tactic| aesop (config := { warnOnNonterminal := false }))

axiom falso : ∀ {α : Sort _}, α

macro "falso" : tactic => `(tactic| exact falso)

@[aesop safe forward (pattern := (↑n : Int))]
axiom nat_pos (n : Nat) : 0 ≤ (↑n : Int)

example (m n : Nat) : (↑m : Int) < 0 ∧ (↑n : Int) > 0 := by
  aesop!
  all_goals
    guard_hyp fwd : 0 ≤ Int.ofNat n
    guard_hyp fwd_2 : 0 ≤ Int.ofNat m
    guard_hyp fwd_3 : 0 ≤ Int.ofNat 0
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

-- When a premise of a forward rule is mentioned in a pattern, it can't also
-- be an immediate argument.

@[aesop safe forward (pattern := (↑x : Int)) (immediate := [y])]
axiom bar (x y : Nat) : True

/--
error: aesop: while registering 'baz' as a forward rule: argument 'x' cannot be immediate since it is already determined by a pattern
-/
#guard_msgs (error) in
@[aesop safe forward (pattern := (↑x : Int)) (immediate := [y, x])]
axiom baz (x y : Nat) : True
