/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- This test can be used to check for memory leaks. It executes Aesop `N`
-- times with a rule set containing a no-op rule (and the builtin rules) and
-- with a limit of 10 goal applications. If everything works properly, the test
-- should only require a small, constant amount of memory.

import Aesop
import Lean

open Lean
open Lean.Elab.Tactic

def N : Nat := 10000

@[aesop safe]
def noopRule : TacticM Unit := return

elab &"memoryStressTest" : tactic =>
  for i in [0:N] do
    evalTactic
      (← `(tactic| try aesop (options := { maxRuleApplications := 10 })))

-- Our very own True, to prevent the Aesop default rules from solving the goal.
structure TT where

set_option maxHeartbeats 0

example : TT := by
  memoryStressTest noopRule
  exact TT.mk
