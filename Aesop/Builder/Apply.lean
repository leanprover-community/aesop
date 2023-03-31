/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

structure ApplyBuilderOptions extends RegularBuilderOptions where
  /-- The transparency used by the rule tactic. -/
  transparency : TransparencyMode
  /-- The transparency used to index the rule. The rule is not indexed unless
  this is `.reducible`. -/
  indexTransparency : TransparencyMode

instance : Inhabited ApplyBuilderOptions where
  default := {
    toRegularBuilderOptions := default
    transparency := .default
    indexTransparency := .reducible
  }

def RuleBuilder.apply (opts : ApplyBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global decl => do
    let tac := .applyConst decl opts.transparency
    let type := (← getConstInfo decl).type
    RuleBuilderOutput.global <$> mkResult tac type
  | RuleBuilderKind.local fvarUserName goal =>
    goal.withContext do
      let tac := RuleTacDescr.applyFVar fvarUserName opts.transparency
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      let result ← mkResult tac type
      return RuleBuilderOutput.local goal result
  where
    mkResult (tac : RuleTacDescr) (type : Expr) : MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.apply
        tac := tac
        indexingMode := ← opts.getIndexingModeM do
          if opts.indexTransparency != .reducible then
            return .unindexed
          else
            IndexingMode.targetMatchingConclusion type
      }

end Aesop
