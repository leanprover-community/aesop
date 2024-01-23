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

end RuleBuilderOptions

def RuleBuilder.constructors : RuleBuilder :=
  ofGlobalRuleBuilder name λ _ decl opts => do
    let info ← RuleBuilder.checkConstIsInductive name decl
    return RuleBuilderResult.regular {
      builder := name
      tac := .constructors info.ctors.toArray opts.constructorsTransparency
      indexingMode := ← getIndexingMode opts info
    }
  where
    name := BuilderName.constructors

    getIndexingMode (opts : RuleBuilderOptions) (info : InductiveVal) :
        MetaM IndexingMode :=
      opts.getIndexingModeM do
        if opts.constructorsIndexTransparency != .reducible then
          return .unindexed
        else
          let mut imodes := Array.mkEmpty info.numCtors
          for ctor in info.ctors do
            let ctorInfo ← getConstInfo ctor
            let imode ← IndexingMode.targetMatchingConclusion ctorInfo.type
            imodes := imodes.push imode
          return .or imodes

end Aesop
