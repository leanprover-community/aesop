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

private def forwardIndexingModeCore (type : Expr)
    (immediate : UnorderedArraySet Nat) (md : TransparencyMode) :
    MetaM IndexingMode := do
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

def forwardIndexingMode (type : Expr)
    (immediate : UnorderedArraySet Nat) (opts : RuleBuilderOptions) :
    MetaM IndexingMode := do
  opts.getIndexingModeM do
    if opts.forwardIndexTransparency != .reducible then
      return .unindexed
    else
      forwardIndexingModeCore type immediate opts.forwardTransparency

end RuleBuilderOptions

namespace RuleBuilder

def getImmediatePremises (stx : Term) (type : Expr) (pat? : Option RulePattern)
    (md : TransparencyMode) :
    Option (Array Name) → MetaM (UnorderedArraySet Nat)
  | none =>
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args, dependent args and args determined by a rule
    -- pattern.
    withTransparency md $ forallTelescopeReducing type λ args _ => do
      let mut result := #[]
      for h : i in [:args.size] do
        if isPatternInstantiated i then
          continue
        let fvarId := (args[i]'h.2).fvarId!
        let ldecl ← fvarId.getDecl
        let isNondep : MetaM Bool :=
          args.allM (start := i + 1) λ arg => do
            let type ← instantiateMVars (← arg.fvarId!.getDecl).type
            return ! type.containsFVar fvarId
        if ← pure ! ldecl.binderInfo.isInstImplicit <&&> isNondep then
          result := result.push i
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate =>
    -- If immediate names are given, we check that corresponding arguments
    -- exists and record these arguments' positions.
    withTransparency md $ forallTelescopeReducing type λ args _ => do
      let mut unseen := immediate.sortDedup (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for h : i in [:args.size] do
        let argName := (← args[i].fvarId!.getDecl).userName
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
    m!"aesop: while registering '{stx}' as a forward rule"

def forwardCore (isDestruct : Bool) : RuleBuilder := λ input => do
  withConstAesopTraceNode .debug (return "forward builder") do
    let builderName : BuilderName := if isDestruct then .destruct else .forward
    let opts := input.options
    if let .all := opts.forwardTransparency then
      throwError "aesop: forward builder currently does not support transparency 'all'"
    let e ← elabRuleTermForApplyLike input.term
    let type ← inferType e
    aesop_trace[debug] "decl type: {type}"
    let pat? ← opts.pattern?.mapM (RulePattern.elab · type)
    let immediate ←
      getImmediatePremises input.term type pat? opts.forwardTransparency
        opts.immediatePremises?
    aesop_trace[debug] "immediate premises: {immediate}"
    let imode ← opts.forwardIndexingMode type immediate
    if let some decl := e.constName? then
      let tac :=
        .forwardConst decl pat? immediate isDestruct opts.forwardTransparency
      return .global $ .base $
        input.toRule builderName decl .global tac imode pat?
    else
      let tac :=
        .forwardTerm input.term pat? immediate isDestruct
          opts.forwardTransparency
      let name ← getRuleName e
      return .global $ .base $
        input.toRule builderName name .local tac imode pat?

def forward : RuleBuilder :=
  forwardCore (isDestruct := false)

def destruct : RuleBuilder :=
  forwardCore (isDestruct := true)

end Aesop.RuleBuilder
