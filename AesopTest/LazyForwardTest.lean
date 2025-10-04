/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Aesop

section errors

example {α β γ : Prop} (h : α → β → γ) (h₁ : α) (h₂ : β) (h : Empty) : False := by
  set_option aesop.dev.statefulForward false in
  --set_option trace.aesop true in
  set_option trace.aesop true in
  aesop (add safe forward h)

end errors

variable {i j k l m n o p : Type}

-- def i : Type := sorry
-- def j : Type := sorry
-- def k : Type := sorry
-- def l : Type := sorry
-- def m : Type := sorry
-- def n : Type := sorry
-- def o : Type := sorry
-- def p : Type := sorry

def myProp {I J : Type} (a : I) (b : J) : Prop := sorry

theorem myThm (a : i) (b : j) (c : k) (d : l) :
    myProp a b ↔ myProp c d := by
  constructor
  · intro hab
    exact hab
  sorry

-- #check Aesop.BuiltinRules.empty_false

example (h : Empty) : False := by
  -- set_option aesop.dev.statefulForward true in
  -- set_option trace.profiler.threshold 0 in
  -- set_option trace.profiler true in
  -- set_option trace.aesop true in
  aesop

example (a : i) (b : j) (c : k) (d : l) (e : m) (f : n) (g : o) (h : p) :
    myProp a b ↔ myProp c d := by
  -- set_option aesop.dev.statefulForward true in
  -- set_option trace.profiler.threshold 0 in
  -- set_option trace.profiler true in
  -- set_option trace.aesop.forward true in
  aesop (add unsafe forward [myThm])

example : True := by
  -- set_option trace.aesop true in
  aesop

example (a : i) (b : j) (c : k) (d : l) (e : m) (f : n) (g : o) (h : p) :
    True := by
  -- set_option aesop.dev.statefulForward true in
  -- set_option trace.profiler.threshold 0 in
  -- set_option trace.profiler true in
  -- set_option trace.aesop true in
  aesop (add safe forward [myThm, True.intro])

example (a : i) (b : j) (c : k) (d : l) (e : m) :
    False := by
  -- set_option aesop.dev.statefulForward true in
  -- set_option trace.profiler.threshold 0 in
  -- set_option trace.profiler true in
  set_option trace.aesop.forward true in
  try aesop (add unsafe forward [myThm])
  sorry


example (a b c d : Nat) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  --set_option trace.profiler true in
  set_option trace.aesop.forward true in
  set_option aesop.dev.statefulForward true in
  aesop (add unsafe forward Nat.le_trans)

/-
This situation occurs in the case of `StdBasisMatrix.mul_same`. This is a deprecated lemma,
to the proof is simply given by `theorem StdBasisMatrix.mul_same : someProp := newTheoremName`.

The problem is that `newTheoremName` quantifies over types. Specifically,

  {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type u_6} [DecidableEq l] [DecidableEq m]
  [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α] (c : α) (i : l) (j : m) (k : n) (d : α)

This gives many possible partial matches - even though proof should simply be the application
of `newTheoremName`.

In the example above there are (according to the metadata `4^4` possible partial matches),
for `StdBasisMatrix.mul_same` its `43904 = 2^7 * 7^3` (Which I'm sure we can explain the number).
In any casem in the simplified example, any of the `4` variables can go in any of the `4` slots.

Thoughts:
- `simp_all` should run before any forward reasoning takes place (This would solve this specific problem (Note not this example I mean `StdBasisMatrix.mul_same`).)
- It's kind of unfortunate that given `(a : i) (i : Type)` hypotheses like `inst✝ : Semiring α : Type` will get matched.
- Overall this is a terrible forward rule - very general hypotheses + very specific thm. Maybe it would be interesting to run the benchmark where we add the rules both backwards and forwards and then interweave the process of both?
- It is not clear to me why `oldForward` is faster, maybe it's running other stuff before trying to do forward reasoning? Indeed, if you run `saturate` than old is slower.

I want to create the forward state associated to a rule only when we get for the first
time to its phase.

-/
