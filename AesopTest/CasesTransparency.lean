/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := False

def U := T

example (h : False) : α := by
  aesop

example (h : T) : α := by
  fail_if_success aesop (options := { terminal := true })
  fail_if_success
    aesop (add safe (cases (transparency! := reducible)) False)
      (options := { terminal := true })
  fail_if_success
    aesop (add safe (cases (transparency := default)) False)
      (options := { terminal := true })
  aesop (add safe (cases (transparency! := default)) False)

example (h : U) : α := by
  aesop (add safe (cases (transparency! := default)) False)
