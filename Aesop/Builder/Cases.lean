/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic
import Aesop.RuleTac.Cases

open Lean
open Lean.Meta

namespace Aesop

namespace CasesPattern

def check (decl : Name) (p : CasesPattern) : MetaM Unit :=
  withoutModifyingState do
    let p ← p.toExpr
    unless p.isAppOf' decl do
      throwError "expected pattern '{p}' ({toString p}) to be an application of '{decl}'"

def toIndexingMode (p : CasesPattern) : MetaM IndexingMode :=
  withoutModifyingState do
    .hyps <$> DiscrTree.mkPath (← p.toExpr) discrTreeConfig

end CasesPattern


namespace RuleBuilderOptions

def casesTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .reducible

def casesIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

def casesPatterns (opts : RuleBuilderOptions) : Array CasesPattern :=
  opts.casesPatterns?.getD #[]

def casesIndexingMode (decl : Name) (opts : RuleBuilderOptions) :
    MetaM IndexingMode :=
  opts.getIndexingModeM do
    if opts.casesIndexTransparency != .reducible then
      return .unindexed
    let casesPatterns := opts.casesPatterns
    if casesPatterns.isEmpty then
      IndexingMode.hypsMatchingConst decl
    else
      .or <$> casesPatterns.mapM (·.toIndexingMode)

def casesTarget (decl : Name) (opts : RuleBuilderOptions) : CasesTarget :=
  let casesPatterns := opts.casesPatterns
  if opts.casesPatterns.isEmpty then
    .decl decl
  else
    .patterns casesPatterns

end RuleBuilderOptions


def RuleBuilder.cases : RuleBuilder := λ input => do
    if input.phase == .norm then throwError
      "cases builder cannot currently be used for norm rules."
      -- TODO `Meta.cases` may assign and introduce metavariables.
      -- (Specifically, it can *replace* existing metavariables, which Aesop
      -- counts as an assignment and an introduction.)
    let inductiveInfo ← elabInductiveRuleIdent .cases input.term
    let decl := inductiveInfo.name
    let opts := input.options
    opts.casesPatterns.forM (·.check decl)
    let imode ← opts.casesIndexingMode decl
    let target := opts.casesTarget decl
    let tac := .cases target opts.casesTransparency inductiveInfo.isRec
    return .global $ .base $ input.toRule .cases decl .global tac imode none

end Aesop
