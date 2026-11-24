/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/

import Aesop

-- Tests for the option `squeezeTerminalSimp` (issue #231).

set_option aesop.check.all true

-- A terminal `simp_all` is squeezed by default...

/--
info: Try this:

  [apply]     intro a_1 a_2
    simp_all only [ne_eq, List.mem_cons, or_self, not_false_eq_true]
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  aesop?

-- ... and printed without `only` if the option is `false`.

/--
info: Try this:

  [apply]     intro a_1 a_2
    simp_all
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  aesop? (config := { squeezeTerminalSimp := false })

-- Lemmas outside the default simp set are kept.

def myId (n : Nat) : Nat := n

theorem myId_eq (n : Nat) : myId n = n := rfl

/--
info: Try this:

  [apply]   simp_all [myId_eq]
-/
#guard_msgs in
example (n : Nat) : myId n = n := by
  aesop? (add norm simp myId_eq) (config := { squeezeTerminalSimp := false })

-- Each branch that `simp_all` closes is a terminal call.

open Classical in
/--
info: Try this:

  [apply]     split at h
    next h_1 => simp_all
    next h_1 => simp_all
-/
#guard_msgs in
example (h : if P then A else B) : A ∨ B := by
  aesop? (config := { squeezeTerminalSimp := false })

-- A call that does not close the goal stays squeezed.

inductive MyList (α : Type _)
  | nil
  | cons (hd : α) (tl : MyList α)

namespace MyList

protected def append : (_ _ : MyList α) → MyList α
  | nil, ys => ys
  | cons x xs, ys => cons x (MyList.append xs ys)

instance : Append (MyList α) :=
  ⟨MyList.append⟩

@[simp]
theorem nil_append : nil ++ xs = xs := rfl

@[simp]
theorem cons_append : cons x xs ++ ys = cons x (xs ++ ys) := rfl

@[aesop safe [constructors, cases]]
inductive NonEmpty : MyList α → Prop
  | cons : NonEmpty (cons x xs)

/--
info: Try this:

  [apply]     intro a
    obtain @⟨x, xs_1⟩ := a
    simp_all only [cons_append]
    apply MyList.NonEmpty.cons
-/
#guard_msgs in
theorem nonEmpty_append {xs : MyList α} ys :
    NonEmpty xs → NonEmpty (xs ++ ys) := by
  aesop? (config := { squeezeTerminalSimp := false })

end MyList
