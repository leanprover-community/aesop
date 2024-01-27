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

def getImmediatePremises (name : Name) (type : Expr) (pat? : Option RulePattern)
    (md : TransparencyMode) : Option (Array Name) → MetaM (UnorderedArraySet Nat)
  | none =>
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args, dependent args and args determined by a rule
    -- pattern.
    withTransparency md $ forallTelescopeReducing type λ args _ => do
      if args.isEmpty then
        throwError "{errPrefix}: not a function"
      let mut result := #[]
      for h : i in [:args.size] do
        if isPatternInstantiated i then
          continue
        let fvarId := (args[i]'h.2).fvarId!
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
        let argName := (← (args[i]'h.2).fvarId!.getDecl).userName
        if immediate.contains argName then
          if isPatternInstantiated i then
            throwError "{errPrefix}: argument '{argName}' cannot be immediate since it is already determined by a pattern"
          else
            result := result.push i
            unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "{errPrefix}: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result
where
  isPatternInstantiated (i : Nat) : Bool :=
    let idx? : Option Nat := do ← (← pat?).argMap[i]?
    idx?.isSome

  errPrefix : MessageData :=
    m!"aesop: while registering '{name}' as a forward rule"

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
  withConstAesopTraceNode .debug (return "forward builder") do
  let opts := input.options
  if let .all := opts.forwardTransparency then
    throwError "aesop: forward builder currently does not support transparency 'all'"
  let pat? := input.options.pattern?
  match input.kind with
  | .global decl => do
    let type := (← getConstInfo decl).type
    let immediate ←
      getImmediatePremises decl type pat? opts.forwardTransparency
        opts.immediatePremises?
    let tac :=
      .forwardConst decl pat? immediate isDestruct opts.forwardTransparency
    aesop_trace[debug] "decl type: {type}"
    aesop_trace[debug] "immediate premises: {immediate}"
    .global <$> mkResult opts tac type immediate
  | .«local» fvarUserName goal => do
    goal.withContext do
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      let immediate ←
        getImmediatePremises fvarUserName type pat? opts.forwardTransparency
          opts.immediatePremises?
      let tac :=
        .forwardFVar fvarUserName pat? immediate isDestruct
          opts.forwardTransparency
        aesop_trace[debug] "fvar type: {type}"
        aesop_trace[debug] "immediate premises: {immediate}"
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
