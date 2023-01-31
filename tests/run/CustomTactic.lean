/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

def Foo := True

declare_aesop_rule_sets [test]

open Lean.Elab.Tactic in
@[aesop safe (rule_sets [test])]
def myTactic : TacticM Unit := do
  evalTactic $ ← `(tactic| rw [Foo])

example : Foo := by
  fail_if_success aesop (options := { terminal := true })
  aesop (rule_sets [test])
