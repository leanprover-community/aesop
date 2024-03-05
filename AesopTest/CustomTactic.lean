/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

def Foo := True

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Foo := by
  aesop (config := { terminal := true })

example : Foo := by
  simp [Foo]

open Lean.Elab.Tactic in
@[aesop safe]
def myTactic : TacticM Unit := do
  evalTactic $ ← `(tactic| rw [Foo])

example : Foo := by
  set_option aesop.check.script false in
  set_option aesop.check.script.steps false in
  aesop
