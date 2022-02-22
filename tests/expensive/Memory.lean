/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- This test can be used to check for memory leaks. It executes Aesop 10000
-- times with a rule set containing a no-op rule (TODO and the default rules,
-- which we should remove for this test) and a limit of 10 goal applications.
-- If everything works properly, the test should only require a small,
-- constant amount of memory.

import Aesop
import Lean

open Lean
open Lean.Elab.Tactic

def noopRule : Aesop.SimpleRuleTac := λ input => do
  return { goals := #[(input.goal, none)] }

syntax (name := memoryStressTest) "memoryStressTest" ident : tactic

@[tactic memoryStressTest]
def evalMemoryStressTest : Tactic
| `(tactic| memoryStressTest $rule:ident) =>
  for i in [0:10000] do
    evalTactic (← `(tactic| try aesop (add safe $rule:ident tactic) (options := { maxRuleApplications := 10, maxRuleApplicationDepth := 10, maxGoals := 0 })))
| _ => unreachable!

-- Our very own True, to prevent the Aesop default rules from solving the goal.
structure TT where

set_option maxHeartbeats 0

example : TT := by
  memoryStressTest noopRule
  exact TT.mk
