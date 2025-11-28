/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.RuleTac.Basic
public import Aesop.Script.SpecificTactics

public section

open Lean Lean.Meta

namespace Aesop.RuleTac

/--
This `RuleTac` is applied once to the root goal, before any other rules are
tried.
-/
def preprocess : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let ((mvarId, _), steps) ← renameInaccessibleFVarsS input.goal |>.run
  let diff := {
    oldGoal := input.goal
    newGoal := mvarId
    addedFVars := ∅
    removedFVars := ∅
    targetChanged := false
  }
  return (#[{ diff }], steps, none)

end Aesop.RuleTac
