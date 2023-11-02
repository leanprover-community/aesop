/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

-- Somewhat inefficient since `foldConsts` doesn't short-circuit.
def hasConst (c : Name) (e : Expr) : Bool :=
  e.foldConsts (init := false) λ c' acc => acc || c' == c

def checkUnfoldableConst (decl : Name) : MetaM Unit :=
  withoutModifyingState do
    let e ← mkConstWithFreshMVarLevels decl
    let t := (← getConstInfo decl).type
    let unfoldThm? ← getUnfoldEqnFor? decl
    forallTelescope t λ args _ => do
      let testExpr := mkAppN e args
      let unfoldResult ←
        unfoldMany (if · == decl then some unfoldThm? else none) testExpr
      match unfoldResult with
      | .unchanged =>
        throwError "Declaration '{decl}' cannot be unfolded."
      | .changed e' _ =>
        if hasConst decl e' then
          throwError "Recursive definition '{decl}' cannot be used as an unfold rule (it would be unfolded infinitely often). Try adding a simp rule for it."

def unfold : RuleBuilder :=
  ofGlobalRuleBuilder .unfold λ _ decl => do
    checkUnfoldableConst decl
    return .unfold { decl, unfoldThm? := ← getUnfoldEqnFor? decl }

end Aesop.RuleBuilder
