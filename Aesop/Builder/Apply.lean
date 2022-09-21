/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

def apply (opts : RegularBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global decl => do
    let tac := .applyConst decl
    let type := (← getConstInfo decl).type
    RuleBuilderOutput.global <$> mkResult tac type
  | RuleBuilderKind.local fvarUserName goal =>
    goal.withContext do
      let tac := RuleTacDescr.applyFVar fvarUserName
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      let result ← mkResult tac type
      return RuleBuilderOutput.local goal result
  where
    mkResult (tac : RuleTacDescr) (type : Expr) : MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.apply
        tac := tac
        indexingMode := ← opts.getIndexingModeM $
          IndexingMode.targetMatchingConclusion type
        mayUseBranchState := false
      }

end Aesop.RuleBuilder
