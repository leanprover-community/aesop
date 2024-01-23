/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

example (h : False) : α := by
  aesop

def T := False

example (h : T) : α := by
  fail_if_success aesop (config := { terminal := true })
  fail_if_success
    aesop (add safe cases (transparency! := reducible) False)
      (config := { terminal := true })
  fail_if_success
    aesop (add safe cases (transparency := default) False)
      (config := { terminal := true })
  aesop (add safe cases (transparency! := default) False)

def U := T

example (h : U) : α := by
  aesop (add safe cases (transparency! := default) False)
