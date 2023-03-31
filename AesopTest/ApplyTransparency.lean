/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := True

example : T := by
  fail_if_success
    aesop (add safe apply True.intro) (options := { terminal := true })
  fail_if_success
    aesop (add safe (apply (transparency := default)) True.intro)
      (options := { terminal := true })
  aesop (add safe (apply (transparency! := default)) True.intro)

@[irreducible] def U := T

example : U := by
  fail_if_success
    aesop (add safe apply True.intro) (options := { terminal := true })
  fail_if_success
    aesop (add safe (apply (transparency := default)) True.intro)
      (options := { terminal := true })
  fail_if_success
    aesop (add safe (apply (transparency! := default)) True.intro)
      (options := { terminal := true })
  aesop (add safe (apply (transparency! := all)) True.intro)
