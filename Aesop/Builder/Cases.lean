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
    .hyps <$> DiscrTree.mkPathWithTransparency (← p.toExpr) indexingTransparency

end CasesPattern


structure CasesBuilderOptions extends RegularBuilderOptions where
  patterns : Array CasesPattern

namespace CasesBuilderOptions

protected def default : CasesBuilderOptions where
  toRegularBuilderOptions := .default
  patterns := #[]

def indexingMode (decl : Name) (opts : CasesBuilderOptions) :
    MetaM IndexingMode :=
  opts.getIndexingModeM do
    if opts.patterns.isEmpty then
      IndexingMode.hypsMatchingConst decl
    else
      .or <$> opts.patterns.mapM (·.toIndexingMode)

def target (decl : Name) (opts : CasesBuilderOptions) : CasesTarget :=
  if opts.patterns.isEmpty then
    .decl decl
  else
    .patterns opts.patterns


end CasesBuilderOptions


def RuleBuilder.cases (opts : CasesBuilderOptions) : RuleBuilder :=
  RuleBuilder.ofGlobalRuleBuilder BuilderName.cases λ phase decl => do
    if let (.norm) := phase then throwError
      "cases builder cannot currently be used for norm rules."
      -- TODO `Meta.cases` may assign and introduce metavariables.
      -- (Specifically, it can *replace* existing metavariables, which Aesop
      -- counts as an assignment and an introduction.)
    let inductInfo ← RuleBuilder.checkConstIsInductive name decl
    opts.patterns.forM (·.check decl)
    let indexingMode ← opts.indexingMode decl
    let target := opts.target decl
    return RuleBuilderResult.regular {
      builder := name
      tac := .cases target (isRecursiveType := inductInfo.isRec)
      indexingMode
      mayUseBranchState := false
    }
  where
    name := BuilderName.cases

end Aesop
