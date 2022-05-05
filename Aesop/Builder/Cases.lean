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
    if let (.norm) := phase then throwError
      "aesop: cases builder cannot currently be used for norm rules."
      -- TODO `Meta.cases` may assign and introduce metavariables.
      -- (Specifically, it can *replace* existing metavariables, which Aesop
      -- counts as an assignment and an introduction.)
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
