/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

def Foo := True

example : Foo := by
  fail_if_success aesop (options := { terminal := true })
  simp [Foo]

open Lean.Elab.Tactic in
@[aesop safe]
def myTactic : TacticM Unit := do
  evalTactic $ ← `(tactic| rw [Foo])

example : Foo := by
  set_option aesop.check.script false in
  set_option aesop.check.script.steps false in
  aesop
