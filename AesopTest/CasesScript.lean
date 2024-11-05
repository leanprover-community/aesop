/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop 50% cases]
inductive FancyAnd (α β : Prop) : Prop
  | dummy (p : Empty)
  | and (a : α) (b : β)

/--
info: Try this:
  apply And.intro
  ·
    cases h with
    | dummy p =>
      have fwd : False := Aesop.BuiltinRules.empty_false p
      simp_all only
    | and a b => simp_all only
  ·
    cases h with
    | dummy p =>
      have fwd : False := Aesop.BuiltinRules.empty_false p
      simp_all only
    | and a b => simp_all only
-/
#guard_msgs in
example {α β} (h : FancyAnd α β) : α ∧ β := by
  aesop?

@[aesop safe cases (cases_patterns := [All _ [], All _ (_ :: _)])]
inductive All (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons : P x → All P xs → All P (x :: xs)

@[aesop 99% constructors]
structure MyTrue : Prop

/--
info: Try this:
  rcases h with ⟨⟩ | @⟨x_1, xs_1, a, a_1⟩
  apply MyTrue.mk
-/
#guard_msgs in
example {P : α → Prop} (h : All P (x :: xs)) : MyTrue := by
  aesop?
