/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Apply

open Lean
open Lean.Meta

namespace Aesop

def RuleBuilder.constructors (opts : RegularBuilderOptions) : RuleBuilder :=
  ofGlobalRuleBuilder name λ _ decl => do
    let info ← RuleBuilder.checkConstIsInductive name decl
    return RuleBuilderResult.regular {
      builder := name
      tac := .constructors info.ctors.toArray
      indexingMode := ← opts.getIndexingModeM $ getIndexingMode info
      mayUseBranchState := false
    }
  where
    name := BuilderName.constructors

    getIndexingMode (info : InductiveVal) : MetaM IndexingMode := do
      let mut imodes := Array.mkEmpty info.numCtors
      for ctor in info.ctors do
        let ctorInfo ← getConstInfo ctor
        let imode ← IndexingMode.targetMatchingConclusion ctorInfo.type
        imodes := imodes.push imode
      return .or imodes

end Aesop
