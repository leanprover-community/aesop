/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Lean

open Lean Lean.Meta Lean.Elab.Tactic

set_option aesop.check.all true

-- When rules add declarations to the environment, Aesop must copy these
-- declarations during proof extraction.

def falso : TacticM Unit := do
  addDecl $ .axiomDecl {
    name := `someaxiom
    levelParams := []
    type := mkConst ``False
    isUnsafe := false
  }
  closeMainGoal (mkConst `someaxiom)

example : False := by
  aesop (add safe falso)

-- A more complex example with dependencies between the rules.

def falso₂ : TacticM Unit := do
  addDecl $ .axiomDecl {
    name := `someaxiom₂
    levelParams := []
    type := ← mkArrow (mkConst ``Nat) (mkConst ``False)
    isUnsafe := false
  }
  addDecl $ .defnDecl {
    name := `fromsomeaxiom₂
    levelParams := []
    type := mkConst ``False
    value := mkApp (mkConst `someaxiom₂) (mkConst ``Nat.zero)
    hints := .regular 0
    safety := .safe
  }
  closeMainGoal (mkConst `fromsomeaxiom₂)

example : False := by
  aesop (add safe falso₂)
