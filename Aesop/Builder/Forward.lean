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
  opts.transparency?.getD .reducible

def forwardIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

namespace RuleBuilder

def getForwardIndexingMode (type : Expr)
    (immediate : UnorderedArraySet PremiseIndex) : MetaM IndexingMode := do
  let immediate := immediate.toArray.map (·.toNat)
  match immediate.max? with
  | some i =>
    withoutModifyingState do
      let (args, _, _) ← withReducible $ forallMetaTelescopeReducing type
      match args[i]? with
      | some arg =>
        let argT := (← arg.mvarId!.getDecl).type
        let keys ← mkDiscrTreePath argT
        return .hyps keys
      | none => throwError
        "aesop: internal error: immediate arg for forward rule is out of range"
  | none => return .unindexed

def getImmediatePremises  (type : Expr) (pat? : Option RulePattern) :
    Option (Array Name) → MetaM (UnorderedArraySet PremiseIndex)
  | none =>
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args, dependent args and args determined by a rule
    -- pattern.
    withReducible $ forallTelescopeReducing type λ args _ => do
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
          result := result.push ⟨i⟩
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate =>
    -- If immediate names are given, we check that corresponding arguments
    -- exists and record these arguments' positions.
    withReducible $ forallTelescopeReducing type λ args _ => do
      let mut unseen := immediate.sortDedup (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for h : i in [:args.size] do
        let argName := (← args[i].fvarId!.getDecl).userName
        if immediate.contains argName then
          if isPatternInstantiated i then
            throwError "{errPrefix}argument '{argName}' cannot be immediate since it is already determined by a pattern"
          else
            result := result.push ⟨i⟩
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
    (pat? : Option RulePattern) (phase : PhaseSpec) (isDestruct : Bool) :
    MetaM ForwardRule := do
  let expr ← t.expr
  let name ← t.name
  let immediate ← getImmediatePremises (← inferType expr) pat? immediate?
  let info ← ForwardRuleInfo.ofExpr expr pat? immediate
  aesop_trace[forward] "rule type:{indentExpr $ ← inferType expr}"
  withConstAesopTraceNode .forward (return m!"slot clusters") do
    aesop_trace[forward] do
      for h : i in [:info.slotClusters.size] do
        let cluster := info.slotClusters[i]
        withConstAesopTraceNode .forward (return m!"cluster {i}") do
          for s in cluster do
            aesop_trace![forward] "slot {s.index} (premise {s.premiseIndex}, deps {s.deps.toArray.qsortOrd}, common {s.common.toArray.qsortOrd}, forward deps {s.forwardDeps.qsortOrd})"
  aesop_trace[forward] "conclusion deps: {info.conclusionDeps}"
  let prio :=
    match phase with
    | .safe info => .normSafe info.penalty
    | .norm info => .normSafe info.penalty
    | .unsafe info => .unsafe info.successProbability
  let builder := if isDestruct then .destruct else .forward
  let name := { phase := phase.phase, name, scope := t.scope, builder }
  return {
    toForwardRuleInfo := info
    term := t.toRuleTerm
    name, prio
  }

def forwardCore (t : ElabRuleTerm) (immediate? : Option (Array Name))
    (pat? : Option RulePattern) (phase : PhaseSpec) (isDestruct : Bool) :
    MetaM LocalRuleSetMember := do
  let builderName : BuilderName := if isDestruct then .destruct else .forward
  let type ← inferType (← t.expr)
  aesop_trace[debug] "decl type: {type}"
  let immediate ← getImmediatePremises type pat? immediate?
  aesop_trace[debug] "immediate premises: {immediate}"
  let imode ← getForwardIndexingMode type immediate
  aesop_trace[debug] "imode: {imode}"
  let tac := .forward t.toRuleTerm immediate isDestruct
  let member := phase.toRule (← t.name) builderName t.scope tac imode pat?
  -- HACK we currently add two rule set members for each forward rule; one
  -- normal, tactic-based rule and one `ForwardRule`. Eventually, only the
  -- `ForwardRule` will remain.
  let forwardRule ← forwardCore₂ t immediate? pat? phase isDestruct
  let member :=
    match member with
    | .normRule r => .normForwardRule forwardRule r
    | .safeRule r => .safeForwardRule forwardRule r
    | .unsafeRule r => .unsafeForwardRule forwardRule r
    | _ => unreachable!
  return .global $ .base member

def forward (isDestruct : Bool) : RuleBuilder := λ input => do
  withConstAesopTraceNode .debug (return "forward builder") do
    let opts := input.options
    let e ← elabRuleTermForApplyLike input.term
    let t := ElabRuleTerm.ofElaboratedTerm input.term e
    let pat? ← opts.pattern?.mapM (RulePattern.elab · e)
    forwardCore t opts.immediatePremises? pat? input.phase
      (isDestruct := isDestruct)

end Aesop.RuleBuilder
