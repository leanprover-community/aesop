/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Apply

open Lean
open Lean.Meta

namespace Aesop

structure ConstructorsBuilderOptions extends RegularBuilderOptions where
  /-- The transparency used by the rule tactic. -/
  transparency : TransparencyMode
  /-- The transparency used to index the rule. The rule is not indexed unless
  this is `.reducible`. -/
  indexTransparency : TransparencyMode

instance : Inhabited ConstructorsBuilderOptions where
  default := {
    toRegularBuilderOptions := default
    transparency := .default
    indexTransparency := .reducible
  }

def RuleBuilder.constructors (opts : ConstructorsBuilderOptions) :
    RuleBuilder :=
  ofGlobalRuleBuilder name λ _ decl => do
    let info ← RuleBuilder.checkConstIsInductive name decl
    return RuleBuilderResult.regular {
      builder := name
      tac := .constructors info.ctors.toArray opts.transparency
      indexingMode := ← opts.getIndexingModeM $ getIndexingMode info
    }
  where
    name := BuilderName.constructors

    getIndexingMode (info : InductiveVal) : MetaM IndexingMode :=
      opts.getIndexingModeM do
        if opts.indexTransparency != .reducible then
          return .unindexed
        else
          let mut imodes := Array.mkEmpty info.numCtors
          for ctor in info.ctors do
            let ctorInfo ← getConstInfo ctor
            let imode ← IndexingMode.targetMatchingConclusion ctorInfo.type
            imodes := imodes.push imode
          return .or imodes

end Aesop
