/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop

structure ForwardBuilderOptions where
  immediateHyps : Option (Array Name)
  clear : Bool
  deriving Inhabited


namespace RuleBuilder

def getImmediatePremises (e : Expr) : Option (Array Name) →
    MetaM (UnorderedArraySet Nat)
  | none => do
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args and dependent args.
    forallTelescope (← inferType e) λ args _ => do
      let mut result := #[]
      for i in [0:args.size] do
        let fvarId := args[i].fvarId!
        let ldecl ← getLocalDecl fvarId
        let isNondep : MetaM Bool :=
          args.allM (start := i + 1) λ arg =>
            return ! (← getLocalDecl arg.fvarId!).type.containsFVar fvarId
        if ← pure ! ldecl.binderInfo.isInstImplicit <&&> isNondep then
          result := result.push i
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate => do
    -- If immediate names are given, we check that corresponding arguments
    -- exists and record these arguments' positions.
    forallTelescope (← inferType e) λ args _ => do
      let mut unseen := immediate.deduplicate (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for i in [0:args.size] do
        let argName := (← getLocalDecl args[i].fvarId!).userName
        if immediate.contains argName then
          result := result.push i
          unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "aesop: while registering '{e}' as a forward rule: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result

def forward (opts : ForwardBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global decl => do
    let immediate ←
      getImmediatePremises (← mkConstWithFreshMVarLevels decl) opts.immediateHyps
    let tac := .forwardConst decl immediate opts.clear
    return RuleBuilderOutput.global $ mkResult tac
  | RuleBuilderKind.local fvarUserName goal => do
    let (goal, #[newHyp]) ← copyRuleHypotheses goal #[fvarUserName]
      | unreachable!
    withMVarContext goal do
      let immediate ← getImmediatePremises (mkFVar newHyp) opts.immediateHyps
      let newUserName := (← getLocalDecl newHyp).userName
      let tac := .forwardFVar newUserName immediate opts.clear
      return RuleBuilderOutput.local (mkResult tac) goal
  where
    mkResult (tac : RuleTacDescr) : RuleBuilderResult :=
      RuleBuilderResult.regular {
        builder := BuilderName.forward
        tac := tac
        indexingMode := IndexingMode.unindexed -- TODO
        mayUseBranchState := true
      }

end Aesop.RuleBuilder
