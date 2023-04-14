/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def T := Unit → Empty

example (h : T) (u : Unit) : α := by
  fail_if_success aesop (options := { terminal := true })
  fail_if_success aesop (add (forward (transparency := reducible)) safe h)
    (options := { terminal := true })
  aesop (add forward safe h)

def U := Unit

example (h : T) (u : U) : α := by
  fail_if_success aesop (options := { terminal := true })
  fail_if_success aesop (add (forward (transparency := reducible)) safe h)
    (options := { terminal := true })
  fail_if_success aesop (add forward safe h) (options := { terminal := true })
  aesop (add (forward (transparency! := default)) safe h)

abbrev V := Unit

example (h : Unit → Empty) (u : V) : α := by
  fail_if_success aesop (options := { terminal := true })
  aesop (add (forward (transparency := reducible)) safe h)
