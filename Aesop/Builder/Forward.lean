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

structure ForwardBuilderOptions extends RegularBuilderOptions where
  immediateHyps : Option (Array Name)
  clear : Bool
  deriving Inhabited

protected def ForwardBuilderOptions.default (clear : Bool) :
    ForwardBuilderOptions where
  toRegularBuilderOptions := .default
  immediateHyps := none
  clear := clear

namespace RuleBuilder

def getImmediatePremises (name : Name) (type : Expr) : Option (Array Name) →
    MetaM (UnorderedArraySet Nat)
  | none => do
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args and dependent args.
    forallTelescope type λ args _ => do
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
    forallTelescope type λ args _ => do
      let mut unseen := immediate.deduplicate (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for i in [0:args.size] do
        let argName := (← getLocalDecl args[i].fvarId!).userName
        if immediate.contains argName then
          result := result.push i
          unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "aesop: while registering '{name}' as a forward rule: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result

private def getIndexingMode (type : Expr) (immediate : UnorderedArraySet Nat) :
    MetaM IndexingMode := do
  let immediate := immediate.toArray
  match immediate.max? with
  | some i =>
    withoutModifyingState do
      let (args, _, _) ← forallMetaTelescope type
      match args.get? i with
      | some arg =>
        let argT ← inferType arg
        let keys ← DiscrTree.mkPathWithTransparency argT indexingTransparency
        return .hyps keys
      | none => throwError
        "aesop: internal error: immediate arg for forward rule is out of range"
  | none => return .unindexed

def forward (opts : ForwardBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | .global decl => do
    let type := (← getConstInfo decl).type
    let immediate ← getImmediatePremises decl type opts.immediateHyps
    let tac := .forwardConst decl immediate opts.clear
    .global <$> mkResult tac type immediate
  | .«local» fvarUserName goal => do
    let (goal, newHyp) ← copyRuleHypothesis goal fvarUserName
    withMVarContext goal do
      let ldecl ← getLocalDecl newHyp
      let immediate ←
        getImmediatePremises ldecl.userName ldecl.type opts.immediateHyps
      let tac := .forwardFVar ldecl.userName immediate opts.clear
      .«local» goal <$> mkResult tac ldecl.type immediate
  where
    mkResult (tac : RuleTacDescr) (type : Expr)
        (immediate : UnorderedArraySet Nat) : MetaM RuleBuilderResult :=
      return .regular {
        builder := .forward
        mayUseBranchState := true
        indexingMode := ← opts.getIndexingModeM $ getIndexingMode type immediate
        tac
      }

end Aesop.RuleBuilder
