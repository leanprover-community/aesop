/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Aesop

section errors

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
warning: declaration uses 'sorry' -/
#guard_msgs in
example {α β γ : Prop} (h : α → β → γ) (h₁ : α) (h₂ : β) : False := by
  aesop (add norm safe h)
  sorry

end errors

variable {i j k l m n o p : Type}

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def myProp {I J : Type} (a : I) (b : J) : Prop := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
theorem myThm (a : i) (b : j) (c : k) (d : l) :
    myProp a b ↔ myProp c d := by
  constructor
  · intro hab
    exact hab
  sorry

example (h : Empty) : False := by
  aesop

example (a : i) (b : j) (c : k) (d : l) (e : m) (f : n) (g : o) (h : p) :
    myProp a b ↔ myProp c d := by
  aesop (add unsafe forward [myThm])

example : True := by
  aesop (add unsafe forward True.intro)

example (a : i) (b : j) (c : k) (d : l) (e : m) (f : n) (g : o) (h : p) :
    True := by
  aesop (add safe forward [myThm, True.intro])

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
example (a : i) (b : j) (c : k) (d : l) (e : m) :
    False := by
  try aesop (add safe forward [myThm])
  sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def a₁ : Nat := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def a₂ : Nat := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
theorem myLe : a₁ ≤ a₂ := sorry

example (c : Nat) (h : a₂ ≤ c) : a₁ ≤ c := by
  aesop (add norm forward myLe, unsafe forward Nat.le_trans)

example (a b c d : Nat) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  aesop (add safe forward [Nat.le_trans])
