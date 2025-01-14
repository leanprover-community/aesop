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
  withoutModifyingState do .hyps <$> mkDiscrTreePath (← p.toExpr)

end CasesPattern


namespace RuleBuilderOptions

def casesTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .reducible

def casesIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

def casesPatterns (opts : RuleBuilderOptions) : Array CasesPattern :=
  opts.casesPatterns?.getD #[]

end RuleBuilderOptions

namespace RuleBuilder

def mkCasesTarget (decl : Name) (casesPatterns : Array CasesPattern) :
    CasesTarget :=
  if casesPatterns.isEmpty then
    .decl decl
  else
    .patterns casesPatterns

def getCasesIndexingMode (decl : Name) (indexMd : TransparencyMode)
    (casesPatterns : Array CasesPattern) : MetaM IndexingMode := do
  if indexMd != .reducible then
    return .unindexed
  if casesPatterns.isEmpty then
    IndexingMode.hypsMatchingConst decl
  else
    .or <$> casesPatterns.mapM (·.toIndexingMode)

def casesCore (info : InductiveVal) (pats : Array CasesPattern)
    (imode? : Option IndexingMode) (md indexMd : TransparencyMode)
    (phase : PhaseSpec) : MetaM LocalRuleSetMember := do
  let decl := info.name
  pats.forM (·.check decl)
  let imode ← imode?.getDM $ getCasesIndexingMode decl indexMd pats
  let target := mkCasesTarget decl pats
  let ctorNames ← mkCtorNames info
  let tac := .cases target md info.isRec ctorNames
  return .global $ .base $ phase.toRule decl .cases .global tac imode none

def cases : RuleBuilder := λ input => do
  let opts := input.options
  if input.phase.phase == .norm then throwError
    "aesop: cases builder cannot currently be used for norm rules."
    -- TODO `Meta.cases` may assign and introduce metavariables.
    -- (Specifically, it can *replace* existing metavariables, which Aesop
    -- counts as an assignment and an introduction.)
  let info ← elabInductiveRuleIdent .cases input.term
  casesCore info opts.casesPatterns opts.indexingMode? opts.casesTransparency
    opts.casesIndexTransparency input.phase

end Aesop.RuleBuilder
