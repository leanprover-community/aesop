/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Aesop

def myProp {i j : Type} (a : i) (b : j) : Prop := sorry

variable {i j k l m n o p : Type}

theorem myThm (a : i) (b : j) (c : k) (d : l) :
    myProp a b ↔ myProp c d := sorry


example (a : i) (b : j) (c : k) (d : l) (e : m) (f : n) (g : o) (h : p) :
    myProp a b ↔ myProp c d := by
  set_option aesop.dev.statefulForward false in
  set_option trace.profiler.threshold 0 in
  set_option trace.profiler true in
  --set_option trace.aesop true in
  set_option maxHeartbeats 20000 in
  -- saturate [myThm]
  -- assumption
  aesop (add safe forward myThm)

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

-/
