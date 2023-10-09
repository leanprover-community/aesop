/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/

-- This test checks whether the output of trace.aesop.proof is
-- copy-and-pastable. When the test breaks because Aesop's output has changed,
-- please copy-and-paste the output to All.split_cons₂ and check whether it
-- still works.

import Aesop

set_option aesop.check.all true

@[aesop safe [constructors, (cases (patterns := [All _ [], All _ (_ :: _)]))]]
inductive All (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

theorem All.split_cons (P : α → Prop) (x : α) (xs : List α) (h : All P (x :: xs))
  : P x ∧ All P xs := by
  set_option trace.aesop.proof true in
  aesop

set_option linter.unusedVariables false in
theorem All.split_cons₂ (P : α → Prop) (x : α) (xs : List α) (h : All P (x :: xs))
  : P x ∧ All P xs :=
      (fun (h_1 : All P (x :: xs)) =>
          ((fun (h_2 : All P (x :: xs)) =>
                (All.casesOn (P := P) (motive := fun a x_1 => x :: xs = a → HEq h x_1 → P x ∧ All P xs) h_2
                    (fun h_1 => List.noConfusion h_1) fun {x_1} {xs_1} a a_1 h_1 =>
                    List.noConfusion h_1 fun head_eq =>
                      Eq.ndrec (motive := fun {x_1} =>
                        ∀ (a : P x_1), xs = xs_1 → HEq h (All.cons (P := P) a a_1) → P x ∧ All P xs)
                        (fun a tail_eq =>
                          Eq.ndrec (motive := fun {xs_1} =>
                            ∀ (a_1 : All P xs_1), HEq h (All.cons (P := P) a a_1) → P x ∧ All P xs)
                            (fun a_1 h_1 =>
                              Eq.ndrec (motive := fun h => P x ∧ All P xs)
                                (of_eq_true (Eq.trans (congr (congrArg And (eq_true a)) (eq_true a_1)) (and_self True)))
                                (Eq.symm (eq_of_heq h_1)))
                            tail_eq a_1)
                        head_eq a :
                  x :: xs = x :: xs → HEq h h_2 → P x ∧ All P xs))
              h_1 :
            x :: xs = x :: xs → HEq h h_1 → P x ∧ All P xs))
        h (Eq.refl (x :: xs)) (HEq.refl h)
