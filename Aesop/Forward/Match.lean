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

/-- Create a one-element match. `forwardDeps` are the forward dependencies of
slot 0. `conclusionDeps` are the conclusion dependencies of the rule to which
this match belongs. -/
def initial (hyp? : Option FVarId) (subst : Substitution)
    (forwardDeps conclusionDeps : Array PremiseIndex) : Match where
  revElems := [.ofHypAndSubst hyp? subst]
  subst := subst
  level := ⟨0⟩
  forwardDeps := forwardDeps
  conclusionDeps := conclusionDeps

/-- Add a hyp or pattern instantiation to the match. `forwardDeps` are the
forward dependencies of the slot of the extended match, i.e. slot
`m.level + 1`. -/
def addHypOrPatternInst (hyp? : Option FVarId) (subst : Substitution)
    (m : Match) (forwardDeps : Array PremiseIndex) : Match where
  revElems := .ofHypAndSubst hyp? subst :: m.revElems
  subst := m.subst.mergeCompatible subst
  level := m.level + 1
  forwardDeps := forwardDeps
  conclusionDeps := m.conclusionDeps

/-- Returns `true` if the match contains the given hyp. -/
def containsHyp (hyp : FVarId) (m : Match) : Bool :=
  m.revElems.any λ
    | .hyp hyp' => hyp == hyp'
    | .patInst .. => false

/-- Returns `true` if the match contains the given pattern instantiation. -/
def containsPatInst (subst : Substitution) (m : Match) : Bool :=
  m.revElems.any λ
    | .patInst subst' => subst == subst'
    | .hyp .. => false

end Match

namespace CompleteMatch

/-- Given a complete match `m` for `r`, get arguments to `r` contained in the
match's slots and substitution. For non-immediate arguments, we return `none`. -/
def reconstructArgs (r : ForwardRule) (m : CompleteMatch) :
    Array (Option Expr) := Id.run do
  let mut slotHyps : Std.HashMap PremiseIndex FVarId := ∅
  for h : i in [:r.slotClusters.size] do
    let cluster := r.slotClusters[i]
    let some m := m.clusterMatches[i]?
      | panic! s!"match for rule {r.name} is not complete: no cluster match for cluster {i}"
    let hyps := m.revElems.toArray.reverse
    for h' : j in [:cluster.size] do
      let slot := cluster[j]
      let some hyp? := hyps[j]?
        | panic! s!"match for rule {r.name} is not complete: no hyp or pattern instantiation for slot with premise index {slot.premiseIndex} in cluster {i}"
      if let .hyp hyp := hyp? then
        slotHyps := slotHyps.insert slot.premiseIndex hyp

  let mut subst : Substitution := .empty r.numPremiseIndexes
  for m in m.clusterMatches do
    subst := subst.mergeCompatible m.subst

  let mut args := Array.mkEmpty r.numPremises
  for i in [:r.numPremises] do
    if let some hyp := slotHyps.get? ⟨i⟩ then
      args := args.push $ some (.fvar hyp)
    else if let some inst := subst.find? ⟨i⟩ then
      args := args.push $ some inst
    else
      args := args.push none

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
    cm.revElems.foldrM (init := s) λ
      | .patInst .., s => pure s
      | .hyp hyp, s => f s hyp

/-- Fold over the hypotheses contained in a match. -/
def foldHyps (f : σ → FVarId → σ) (init : σ) (m : ForwardRuleMatch) : σ :=
  m.foldHypsM (M := Id) f init

/-- Returns `true` if any hypothesis contained in `m` satisfies `f`. -/
def anyHyp (m : ForwardRuleMatch) (f : FVarId → Bool) : Bool :=
  m.match.clusterMatches.any λ m =>
    m.revElems.any λ
      | .patInst .. => false
      | .hyp hyp => f hyp

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
match is for a `destruct` rule. -/
def apply (goal : MVarId) (m : ForwardRuleMatch) :
    ScriptM (Option (MVarId × FVarId × Array FVarId)) :=
  goal.withContext do
    let name ← getUnusedUserName forwardHypPrefix
    let some prf ← m.getProof goal
      | return none
    let type ← inferType prf
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
