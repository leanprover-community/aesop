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
  SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
    runTacticMAsMetaM tac input.goal

-- Precondition: `decl` has type `TacticM Unit`.
@[implementedBy tacticMImpl]
opaque tacticM (decl : Name) : RuleTac

-- Precondition: `decl` has type `RuleTac`.
unsafe def ruleTacImpl (decl : Name) : RuleTac := λ input => do
  let tac ← evalConst RuleTac decl
  tac input

-- Precondition: `decl` has type `RuleTac`.
@[implementedBy ruleTacImpl]
opaque ruleTac (decl : Name) : RuleTac

-- Precondition: `decl` has type `SimpleRuleTac`.
unsafe def simpleRuleTacImpl (decl : Name) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SimpleRuleTac decl
    tac input

-- Precondition: `decl` has type `SimpleRuleTac`.
@[implementedBy simpleRuleTacImpl]
opaque simpleRuleTac (decl : Name) : RuleTac

end Aesop.RuleTac
