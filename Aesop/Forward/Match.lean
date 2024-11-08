/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.Match.Types
import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Rule
import Aesop.Rule.Forward
import Aesop.RuleTac.Descr
import Aesop.RuleTac.ElabRuleTerm
import Aesop.RuleTac.Forward.Basic
import Aesop.Script.SpecificTactics
import Batteries.Lean.Meta.UnusedNames
import Lean

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- Elaborate the term of a forward rule in the current goal. -/
def elabForwardRuleTerm (goal : MVarId) : RuleTerm → MetaM Expr
  | .const n => mkConstWithFreshMVarLevels n
  | .term stx =>
    (withFullElaboration $ elabRuleTermForApplyLikeMetaM goal stx).run'

namespace Match

/-- Create a one-element match. `subst` is the substitution that results from
matching a hypothesis against slot 0, or from a pattern instantiation.
`isPatInst` is `true` if the substitution resulted from a pattern instantiation.
`forwardDeps` are the forward dependencies of slot 0. `conclusionDeps` are the
conclusion dependencies of the rule to which this match belongs. -/
def initial (subst : Substitution) (isPatInst : Bool)
    (forwardDeps conclusionDeps : Array PremiseIndex) : Match where
  subst := subst
  patInstSubsts := if isPatInst then #[subst] else #[]
  level := ⟨0⟩
  forwardDeps := forwardDeps
  conclusionDeps := conclusionDeps

/-- Add a hyp or pattern instantiation to the match. `subst` is the substitution
that results from matching a hypothesis against slot `m.level + 1`, or from the
pattern instantiation. `isPatInst` is `true` if the substitution resulted from
a pattern instantiation. `forwardDeps` are the forward dependencies of slot
`m.level + 1`. -/
def addHypOrPatternInst (subst : Substitution) (isPatInst : Bool)
    (forwardDeps : Array PremiseIndex) (m : Match) : Match where
  subst := m.subst.mergeCompatible subst
  patInstSubsts :=
    if isPatInst then m.patInstSubsts.push subst else m.patInstSubsts
  level := m.level + 1
  forwardDeps := forwardDeps
  conclusionDeps := m.conclusionDeps

/-- Returns `true` if the match contains the given hyp. -/
def containsHyp (hyp : FVarId) (m : Match) : Bool :=
  m.subst.toArray.any (· == some (.fvar hyp))

/-- Returns `true` if the match contains the given pattern instantiation. -/
def containsPatInst (subst : Substitution) (m : Match) : Bool :=
  m.patInstSubsts.any (· == subst)

end Match

namespace CompleteMatch

/-- Given a complete match `m` for `r`, get arguments to `r` contained in the
match's slots and substitution. For non-immediate arguments, we return `none`. -/
def reconstructArgs (r : ForwardRule) (m : CompleteMatch) :
    Array (Option Expr) := Id.run do
  assert! m.clusterMatches.size == r.slotClusters.size
  let mut subst : Substitution := .empty r.numPremiseIndexes
  for m in m.clusterMatches do
    subst := subst.mergeCompatible m.subst
  let mut args := Array.mkEmpty r.numPremises
  for i in [:r.numPremises] do
    args := args.push $ subst.find? ⟨i⟩
  return args

set_option linter.missingDocs false in
protected def toMessageData (r : ForwardRule) (m : CompleteMatch) :
    MessageData :=
  m!"{m.reconstructArgs r |>.map λ | none => m!"_" | some e => m!"{e}"}"

end CompleteMatch

namespace ForwardRuleMatch

instance : ToMessageData ForwardRuleMatch where
  toMessageData m := m!"{m.rule} {m.match.toMessageData m.rule}"

/-- Compare two queue entries by rule priority and rule name. Higher-priority
rules are considered less (since the queues are min-queues). -/
protected def le (m₁ m₂ : ForwardRuleMatch) : Bool :=
  m₁.rule.prio.le m₂.rule.prio ||
  (m₁.rule.prio == m₂.rule.prio && (m₁.rule.name.compare m₂.rule.name).isLE)

/-- Fold over the hypotheses contained in a match. -/
def foldHypsM [Monad M] (f : σ → FVarId → M σ) (init : σ)
    (m : ForwardRuleMatch) : M σ :=
  m.match.clusterMatches.foldlM (init := init) λ s cm =>
    cm.subst.toArray.foldrM (init := s) λ
      | some (.fvar hyp), s => f s hyp
      | _, s => pure s

/-- Fold over the hypotheses contained in a match. -/
def foldHyps (f : σ → FVarId → σ) (init : σ) (m : ForwardRuleMatch) : σ :=
  m.foldHypsM (M := Id) f init

/-- Returns `true` if any hypothesis contained in `m` satisfies `f`. -/
def anyHyp (m : ForwardRuleMatch) (f : FVarId → Bool) : Bool :=
  m.match.clusterMatches.any λ m =>
    m.subst.toArray.any λ
      | some (.fvar hyp) => f hyp
      | _ => false

/-- Get the hypotheses from the match whose types are propositions.  -/
def getPropHyps (m : ForwardRuleMatch) : MetaM (Array FVarId) :=
  m.foldHypsM (init := Array.mkEmpty m.rule.numPremises) λ hs h => do
    if ← isProof (.fvar h) then return hs.push h else return hs

/-- Construct the proof of the new hypothesis represented by `m`. -/
def getProof (goal : MVarId) (m : ForwardRuleMatch) : MetaM (Option Expr) :=
  withConstAesopTraceNode .forward (return m!"proof construction for forward rule match") do
  goal.withContext do
  withNewMCtxDepth do
    aesop_trace[forward] "rule: {m.rule.name}"
    let e ← elabForwardRuleTerm goal m.rule.term
    aesop_trace[forward] "term: {e} : {← inferType e}"
    let (argMVars, binderInfos, _) ←
      withReducible $ forallMetaTelescope (← inferType e)
    let args := m.match.reconstructArgs m.rule
    aesop_trace[forward] "args: {args.map λ | none => m!"_" | some e => m!"{e}"}"
    for arg? in args, mvar in argMVars do
      if let some arg := arg? then
        if ! (← isDefEq arg mvar) then
          throwError "type mismatch during reconstruction of match for forward rule{indentD m!"{m.rule.name}"}\n: expected{indentExpr (← inferType mvar)}\nbut got{indentExpr arg} : {← inferType arg}"
    try
      synthAppInstances `aesop goal argMVars binderInfos
        (synthAssignedInstances := false) (allowSynthFailures := false)
    catch _ =>
      aesop_trace[forward] "instance synthesis failed"
      return none
    let result := (← abstractMVars $ mkAppN e argMVars).expr
    aesop_trace[forward] "result: {result}"
    return result

/-- Apply a forward rule match to a goal. This adds the hypothesis corresponding
to the match to the local context. Returns the new goal, the added hypothesis
and the hypotheses that were removed (if any). Hypotheses may be removed if the
match is for a `destruct` rule. If `skipExisting` is true, the new hypothesis
is only added if there is no hypothesis with a reducibly defeq type already in
the context. -/
def apply (goal : MVarId) (m : ForwardRuleMatch) (skipExisting : Bool) :
    ScriptM (Option (MVarId × FVarId × Array FVarId)) :=
  goal.withContext do
    let name ← getUnusedUserName forwardHypPrefix
    let some prf ← m.getProof goal
      | return none
    let type ← inferType prf
    if skipExisting then
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then
          continue
        if ← withReducible $ withNewMCtxDepth $ isDefEq type ldecl.type then
          return none
    let hyp := { userName := name, value := prf, type }
    let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
      | unreachable!
    if ! m.rule.destruct then
      return some (goal, hyp, #[])
    let usedPropHyps ← goal.withContext $ m.getPropHyps
    let (goal, _) ← tryClearManyS goal usedPropHyps
    return some (goal, hyp, usedPropHyps)

/-- Convert a forward rule match to a rule tactic description. -/
def toRuleTacDescr (m : ForwardRuleMatch) : RuleTacDescr :=
  .forwardMatch m

/-- Convert a forward rule match `m` to a rule. Fails if `mkExtra? m` fails. -/
def toRule? (m : ForwardRuleMatch) (mkExtra? : ForwardRuleMatch → Option α) :
    Option (Rule α) := do
  let extra ← mkExtra? m
  return {
    name := m.rule.name
    indexingMode := .unindexed
    pattern? := none
    tac := m.toRuleTacDescr
    extra
  }

/-- Convert a norm forward rule match to a norm rule. Fails if the match is not
a norm rule match. -/
def toNormRule? (m : ForwardRuleMatch) : Option NormRule :=
  m.toRule? (·.rule.prio.penalty?.map ({ penalty := · }))

/-- Convert a safe forward rule match to a safe rule. Fails if the match is not
a safe rule match. -/
def toSafeRule? (m : ForwardRuleMatch) : Option SafeRule :=
  m.toRule? (·.rule.prio.penalty?.map ({ penalty := ·, safety := .safe }))

/-- Convert an unsafe forward rule match to an unsafe rule. Fails if the match
is not an unsafe rule match. -/
def toUnsafeRule? (m : ForwardRuleMatch) : Option UnsafeRule :=
  m.toRule? (·.rule.prio.successProbability?.map ({ successProbability := · }))

end Aesop.ForwardRuleMatch