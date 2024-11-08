/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

namespace RuleBuilderOptions

def applyTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def applyIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

namespace RuleBuilder

def getApplyIndexingMode (indexMd : TransparencyMode) (type : Expr) :
    MetaM IndexingMode :=
  if indexMd != .reducible then
    return .unindexed
  else
    IndexingMode.targetMatchingConclusion type

def checkNoIff (type : Expr) : MetaM Unit := do
  if aesop.warn.applyIff.get (← getOptions) then
    forallTelescope type λ _ conclusion => do
      if ← testHelper conclusion λ e => return e.isAppOf' ``Iff then
        logWarning m!"Apply builder was used for a theorem with conclusion A ↔ B.\nYou probably want to use the simp builder or create an alias that applies the theorem in one direction.\nUse `set_option aesop.warn.applyIff false` to disable this warning."

def applyCore (t : ElabRuleTerm) (pat? : Option RulePattern)
    (imode? : Option IndexingMode) (md indexMd : TransparencyMode)
    (phase : PhaseSpec) : MetaM LocalRuleSetMember := do
  let e ← t.expr
  let type ← inferType e
  let imode ← imode?.getDM $ getApplyIndexingMode indexMd type
  let tac := .apply t.toRuleTerm md pat?
  return .global $ .base $ phase.toRule (← t.name) .apply t.scope tac imode pat?

def apply : RuleBuilder := λ input => do
  let opts := input.options
  let e ← elabRuleTermForApplyLike input.term
  let t := ElabRuleTerm.ofElaboratedTerm input.term e
  let type ← inferType e
  checkNoIff type
  let pat? ← opts.pattern?.mapM (RulePattern.elab · type)
  applyCore t pat? opts.indexingMode? opts.applyTransparency
    opts.applyIndexTransparency input.phase

end Aesop.RuleBuilder
