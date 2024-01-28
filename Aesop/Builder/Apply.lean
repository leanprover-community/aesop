/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

namespace RuleBuilderOptions

def applyTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def applyIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

def RuleBuilder.apply : RuleBuilder := λ input =>
  let opts := input.options
  match input.kind with
  | RuleBuilderKind.global decl => do
    let tac := .applyConst decl opts.applyTransparency opts.pattern?
    let type := (← getConstInfo decl).type
    RuleBuilderOutput.global <$> mkResult opts tac type
  | RuleBuilderKind.local fvarUserName goal =>
    goal.withContext do
      let tac := .applyFVar fvarUserName opts.applyTransparency opts.pattern?
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      let result ← mkResult opts tac type
      return RuleBuilderOutput.local goal result
  where
    mkResult (opts : RuleBuilderOptions) (tac : RuleTacDescr) (type : Expr) :
        MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.apply
        tac := tac
        indexingMode := ← opts.getIndexingModeM do
          if opts.applyIndexTransparency != .reducible then
            return .unindexed
          else
            IndexingMode.targetMatchingConclusion type
      }

end Aesop
