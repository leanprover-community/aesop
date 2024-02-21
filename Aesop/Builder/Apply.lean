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

def applyIndexingMode (opts : RuleBuilderOptions) (type : Expr) :
    MetaM IndexingMode :=
  opts.getIndexingModeM do
    if opts.applyIndexTransparency != .reducible then
      return .unindexed
    else
      IndexingMode.targetMatchingConclusion type

end RuleBuilderOptions


def RuleBuilder.apply : RuleBuilder := λ input => do
  let opts := input.options
  let e ← elabRuleTermForApplyLike input.term
  let type ← inferType e
  let pat? ← opts.pattern?.mapM (RulePattern.elab · type)
  let imode ← opts.applyIndexingMode type
  if let some decl := e.constName? then
    let tac := .applyConst decl opts.applyTransparency pat?
    return .global $ .base $ input.toRule .apply decl .global tac imode pat?
  else
    let name ← getRuleName e
    let tac := .applyTerm input.term opts.applyTransparency pat?
    return .global $ .base $ input.toRule .apply name .local tac imode pat?

end Aesop
