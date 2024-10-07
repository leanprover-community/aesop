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
        let keys ← mkDiscrTreePath argT
        return .hyps keys
      | none => throwError
        "aesop: internal error: immediate arg for forward rule is out of range"
  | none => return .unindexed

def getForwardIndexingMode (type : Expr) (immediate : UnorderedArraySet Nat)
    (md indexMd : TransparencyMode) : MetaM IndexingMode := do
  if indexMd != .reducible then
    return .unindexed
  else
    forwardIndexingModeCore type immediate md


def getImmediatePremises  (type : Expr) (pat? : Option RulePattern)
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
        let fvarId := args[i].fvarId!
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
            throwError "{errPrefix}argument '{argName}' cannot be immediate since it is already determined by a pattern"
          else
            result := result.push i
            unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "{errPrefix}function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result
where
  isPatternInstantiated (i : Nat) : Bool :=
    let idx? : Option Nat := do ← (← pat?).argMap[i]?
    idx?.isSome

  errPrefix : MessageData :=
    m!"aesop: forward builder: "

def forwardCore₂ (t : ElabRuleTerm) (immediate? : Option (Array Name))
    (pat? : Option RulePattern) (imode? : Option IndexingMode)
    (md indexMd : TransparencyMode) (phase : PhaseSpec) (isDestruct : Bool) :
    MetaM (Option ForwardRule) := do
  -- TODO support all these options
  if immediate?.isSome || pat?.isSome || imode?.isSome || md != .default ||
     indexMd != .reducible || isDestruct then
    return none
  let expr ← t.expr
  let name ← t.name
  let info ← ForwardRuleInfo.ofExpr expr
  if info.numPremises == 0 then
    return none -- Constant forward rules currently don't work.
  let prio :=
    match phase with
    | .safe info => .normSafe info.penalty
    | .norm info => .normSafe info.penalty
    | .unsafe info => .unsafe info.successProbability
  return some {
    toForwardRuleInfo := info
    name := { phase := phase.phase, name, scope := t.scope, builder := .forward }
    term := t.toRuleTerm
    prio
  }

def forwardCore (t : ElabRuleTerm) (immediate? : Option (Array Name))
    (pat? : Option RulePattern) (imode? : Option IndexingMode)
    (md indexMd : TransparencyMode) (phase : PhaseSpec) (isDestruct : Bool) :
    MetaM LocalRuleSetMember := do
  let builderName : BuilderName := if isDestruct then .destruct else .forward
  if let .all := md then
    throwError "aesop: forward builder currently does not support transparency 'all'"
  let type ← inferType (← t.expr)
  aesop_trace[debug] "decl type: {type}"
  let immediate ← getImmediatePremises type pat? md immediate?
  aesop_trace[debug] "immediate premises: {immediate}"
  let imode ← imode?.getDM $ getForwardIndexingMode type immediate md indexMd
  aesop_trace[debug] "imode: {imode}"
  let tac := .forward t.toRuleTerm pat? immediate isDestruct md
  let member := phase.toRule (← t.name) builderName t.scope tac imode pat?
  -- HACK we currently add two rule set members for each forward rule; one
  -- normal, tactic-based rule and one `ForwardRule`. Eventually, only the
  -- `ForwardRule` will remain.
  let forwardRule? ←
    forwardCore₂ t immediate? pat? imode? md indexMd phase isDestruct
  let member :=
    if let some forwardRule := forwardRule? then
      match member with
      | .normRule r => .normForwardRule forwardRule r
      | .safeRule r => .safeForwardRule forwardRule r
      | .unsafeRule r => .unsafeForwardRule forwardRule r
      | _ => member
    else
      member
  return .global $ .base member

def forward (isDestruct : Bool) : RuleBuilder := λ input => do
  withConstAesopTraceNode .debug (return "forward builder") do
    let opts := input.options
    let e ← elabRuleTermForApplyLike input.term
    let t := ElabRuleTerm.ofElaboratedTerm input.term e
    let type ← inferType e
    let pat? ← opts.pattern?.mapM (RulePattern.elab · type)
    forwardCore t opts.immediatePremises? pat? opts.indexingMode?
      opts.forwardTransparency opts.forwardIndexTransparency input.phase
      (isDestruct := isDestruct)

end Aesop.RuleBuilder
