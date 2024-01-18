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

def forwardTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def forwardIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

namespace RuleBuilder

def getImmediatePremises (name : Name) (type : Expr) (md : TransparencyMode) :
    Option (Array Name) → MetaM (UnorderedArraySet Nat)
  | none =>
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args and dependent args.
    withTransparency md $ forallTelescopeReducing type λ args _ => do
      if args.isEmpty then
        throwError "aesop: while registering '{name}' as a forward rule: not a function"
      let mut result := #[]
      for h : i in [:args.size] do
        have h : i < args.size := h.2
        let fvarId := args[i].fvarId!
        let ldecl ← fvarId.getDecl
        let isNondep : MetaM Bool :=
          args.allM (start := i + 1) λ arg =>
            return ! (← arg.fvarId!.getDecl).type.containsFVar fvarId
        if ← pure ! ldecl.binderInfo.isInstImplicit <&&> isNondep then
          result := result.push i
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate =>
    -- If immediate names are given, we check that corresponding arguments
    -- exists and record these arguments' positions.
    withTransparency md $ forallTelescopeReducing type λ args _ => do
      let mut unseen := immediate.sortAndDeduplicate (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for h : i in [:args.size] do
        have h : i < args.size := by simp_all [Membership.mem]
        let argName := (← args[i].fvarId!.getDecl).userName
        if immediate.contains argName then
          result := result.push i
          unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "aesop: while registering '{name}' as a forward rule: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result

private def getIndexingMode (type : Expr) (immediate : UnorderedArraySet Nat)
    (md : TransparencyMode) : MetaM IndexingMode := do
  let immediate := immediate.toArray
  match immediate.max? with
  | some i =>
    withoutModifyingState do
      let (args, _, _) ← withTransparency md $ forallMetaTelescopeReducing type
      match args.get? i with
      | some arg =>
        let argT := (← arg.mvarId!.getDecl).type
        let keys ← DiscrTree.mkPath argT discrTreeConfig
        return .hyps keys
      | none => throwError
        "aesop: internal error: immediate arg for forward rule is out of range"
  | none => return .unindexed

def forwardCore (isDestruct : Bool) : RuleBuilder := λ input => do
  let opts := input.options
  if let .all := opts.forwardTransparency then
    throwError "aesop: forward builder currently does not support transparency 'all'"
  match input.kind with
  | .global decl => do
    let type := (← getConstInfo decl).type
    let immediate ←
      getImmediatePremises decl type opts.forwardTransparency
        opts.immediatePremises?
    let tac :=
      .forwardConst decl immediate isDestruct opts.forwardTransparency
    .global <$> mkResult opts tac type immediate
  | .«local» fvarUserName goal => do
    goal.withContext do
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      let immediate ←
        getImmediatePremises fvarUserName type opts.forwardTransparency
          opts.immediatePremises?
      let tac :=
        .forwardFVar fvarUserName immediate isDestruct opts.forwardTransparency
      .«local» goal <$> mkResult opts tac type immediate
  where
    mkResult (opts : RuleBuilderOptions) (tac : RuleTacDescr) (type : Expr)
        (immediate : UnorderedArraySet Nat) : MetaM RuleBuilderResult := do
      let indexingMode ← opts.getIndexingModeM do
        if opts.forwardIndexTransparency != .reducible then
          return .unindexed
        else
          getIndexingMode type immediate opts.forwardTransparency
      return .regular {
        builder := .forward
        tac, indexingMode
      }

def forward : RuleBuilder :=
  forwardCore (isDestruct := false)

def destruct : RuleBuilder :=
  forwardCore (isDestruct := true)

end Aesop.RuleBuilder
