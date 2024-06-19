/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Apply

open Lean
open Lean.Meta

namespace Aesop.RuleBuilderOptions

def constructorsTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def constructorsIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

def constructorsIndexingMode (opts : RuleBuilderOptions) (info : InductiveVal) :
    MetaM IndexingMode :=
  opts.indexingMode?.getDM do
    if opts.constructorsIndexTransparency != .reducible then
      return .unindexed
    else
      let mut imodes := Array.mkEmpty info.numCtors
      for ctor in info.ctors do
        let ctorInfo ← getConstInfo ctor
        let imode ← IndexingMode.targetMatchingConclusion ctorInfo.type
        imodes := imodes.push imode
      return .or imodes

end RuleBuilderOptions

def RuleBuilder.constructors : RuleBuilder := λ input => do
  let info ← elabInductiveRuleIdent .constructors input.term
  let opts := input.options
  let tac := .constructors info.ctors.toArray opts.constructorsTransparency
  let imode ← opts.constructorsIndexingMode info
  return .global $ .base $
    input.toRule .constructors info.name .global tac imode none

end Aesop
