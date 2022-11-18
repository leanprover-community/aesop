/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM)

namespace Aesop.RuleTac

-- Precondition: `decl` has type `TacticM Unit`.
unsafe def tacticMImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
    let goals ← runTacticMAsMetaM input.goal tac
    return (goals.toArray, .unknown decl)

-- Precondition: `decl` has type `TacticM Unit`.
@[implemented_by tacticMImpl]
opaque tacticM (decl : Name) : RuleTac

-- Precondition: `decl` has type `RuleTac`.
unsafe def ruleTacImpl (decl : Name) : RuleTac := λ input => do
  let tac ← evalConst RuleTac decl
  tac input

-- Precondition: `decl` has type `RuleTac`.
@[implemented_by ruleTacImpl]
opaque ruleTac (decl : Name) : RuleTac

-- Precondition: `decl` has type `SimpleRuleTac`.
unsafe def singleRuleTacImpl (decl : Name) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SingleRuleTac decl
    tac input

-- Precondition: `decl` has type `SimpleRuleTac`.
@[implemented_by singleRuleTacImpl]
opaque singleRuleTac (decl : Name) : RuleTac

end Aesop.RuleTac
