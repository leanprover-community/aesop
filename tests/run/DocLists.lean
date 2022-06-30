/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- NOTE: This file contains examples for, and therefore should be kept in sync
-- with, the README.

import Aesop

set_option aesop.check.all true

inductive MyList (α : Type _)
  | nil
  | cons (hd : α) (tl : MyList α)

namespace MyList

protected def append : (_ _ : MyList α) → MyList α
  | nil, ys => ys
  | cons x xs, ys => cons x (MyList.append xs ys)

instance : Append (MyList α) :=
  ⟨MyList.append⟩

-- TODO there should be a more convenient way to do this, similar to @[simps]
-- in Lean 3.
@[simp]
theorem nil_append : nil ++ xs = xs := rfl

@[simp]
theorem cons_append : cons x xs ++ ys = cons x (xs ++ ys) := rfl

declare_aesop_rule_sets [MyList.NonEmpty]

@[aesop safe (rule_sets [MyList.NonEmpty]) [constructors, cases]]
inductive NonEmpty : MyList α → Prop
  | cons : NonEmpty (cons x xs)

@[aesop safe]
theorem nonEmpty_append {xs : MyList α} ys :
    NonEmpty xs → NonEmpty (xs ++ ys) := by
  aesop (rule_sets [MyList.NonEmpty])

example {α : Type _} {xs : MyList α} ys zs :
    NonEmpty xs → NonEmpty (xs ++ ys ++ zs) := by
  aesop

theorem nil_not_NonEmpty (xs : MyList α) : xs = nil → ¬ NonEmpty xs := by
  aesop (add 10% cases MyList, norm unfold Not) (rule_sets [MyList.NonEmpty])

@[aesop norm]
theorem append_nil {xs : MyList α} :
    xs ++ nil = xs := by
  induction xs <;> aesop

theorem append_assoc {xs ys zs : MyList α} :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs <;> aesop

end MyList
