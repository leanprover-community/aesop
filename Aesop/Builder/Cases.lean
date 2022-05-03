/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop
def RuleBuilder.cases : RuleBuilder :=
  RuleBuilder.ofGlobalRuleBuilder BuilderName.cases λ phase decl => do
    let inductInfo ← RuleBuilder.checkConstIsInductive name decl
    return RuleBuilderResult.regular {
      builder := name
      tac := .cases decl (isRecursiveType := inductInfo.isRec)
      indexingMode := ← IndexingMode.hypsMatchingConst decl
      mayUseBranchState := false
    }
  where
    name := BuilderName.cases

end Aesop
