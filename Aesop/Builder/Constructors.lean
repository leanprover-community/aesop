/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Apply

open Lean
open Lean.Meta

namespace Aesop

def GlobalRuleTacBuilder.constructors (constructorNames : Array Name) :
    GlobalRuleTacBuilder := do
  return {
    tac := RuleTac.applyConsts constructorNames
    descr := GlobalRuleTacBuilderDescr.constructors constructorNames
  }

def RuleBuilder.constructors : RuleBuilder :=
  ofGlobalRuleBuilder name λ phase decl => do
    let info ← RuleBuilder.checkConstIsInductive name decl
    return RuleBuilderResult.regular {
      builder := name
      tac := ← GlobalRuleTacBuilder.constructors info.ctors.toArray
      indexingMode := IndexingMode.unindexed -- TODO optimise as soon as we have OR for IndexingModes
      mayUseBranchState := false
    }
  where
    name := BuilderName.constructors

end Aesop
