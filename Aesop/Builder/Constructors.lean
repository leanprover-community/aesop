/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilderOptions

def constructorsTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def constructorsIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

namespace RuleBuilder

def getConstructorsIndexingMode (indexMd : TransparencyMode)
    (info : InductiveVal) : MetaM IndexingMode := do
  if indexMd != .reducible then
    return .unindexed
  else
    let mut imodes := Array.mkEmpty info.numCtors
    for ctor in info.ctors do
      let ctorInfo ← getConstInfo ctor
      let imode ← IndexingMode.targetMatchingConclusion ctorInfo.type
      imodes := imodes.push imode
    return .or imodes

def constructorsCore (info : InductiveVal) (imode? : Option IndexingMode)
    (md indexMd : TransparencyMode) (phase : PhaseSpec) :
    MetaM LocalRuleSetMember := do
  let tac := .constructors info.ctors.toArray md
  let imode ← imode?.getDM $ getConstructorsIndexingMode indexMd info
  return .global $ .base $
    phase.toRule info.name .constructors .global tac imode none

def constructors : RuleBuilder := λ input => do
  let info ← elabInductiveRuleIdent .constructors input.term
  let opts := input.options
  constructorsCore info opts.indexingMode? opts.constructorsTransparency
    opts.constructorsIndexTransparency input.phase

end Aesop.RuleBuilder
