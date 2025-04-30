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
matching a hypothesis against slot 0, or from a pattern substitution.
`isPatSubst` is `true` if the substitution resulted from a rule pattern.
`forwardDeps` are the forward dependencies of slot 0. `conclusionDeps` are the
conclusion dependencies of the rule to which this match belongs. -/
def initial (subst : Substitution) (isPatSubst : Bool)
    (forwardDeps conclusionDeps : Array PremiseIndex) : Match where
  subst := subst
  patInstSubsts := if isPatSubst then #[subst] else #[]
  level := ⟨0⟩
  forwardDeps := forwardDeps
  conclusionDeps := conclusionDeps

/-- Add a hyp or pattern substitution to the match. `subst` is the substitution
that results from matching a hypothesis against slot `m.level + 1`, or from the
pattern. `isPatSubst` is `true` if the substitution resulted from a pattern
substitution. `forwardDeps` are the forward dependencies of slot
`m.level + 1`. -/
def addHypOrPatSubst (subst : Substitution) (isPatSubst : Bool)
    (forwardDeps : Array PremiseIndex) (m : Match) : Match where
  subst := m.subst.mergeCompatible subst
  patInstSubsts :=
    if isPatSubst then m.patInstSubsts.push subst else m.patInstSubsts
  level := m.level + 1
  forwardDeps := forwardDeps
  conclusionDeps := m.conclusionDeps

/-- Returns `true` if the match contains the given hyp. -/
def containsHyp (hyp : FVarId) (m : Match) : Bool :=
  m.subst.premises.any (·.any (·.toExpr.containsFVar hyp))

/-- Returns `true` if the match contains the given pattern substitution. -/
def containsPatSubst (subst : Substitution) (m : Match) : Bool :=
  m.patInstSubsts.any (· == subst)

end Match

namespace CompleteMatch

/-- Given a complete match `m` for `r`, get arguments to `r` contained in the
match's slots and substitution. For non-immediate arguments, we return `none`.
The returned levels are suitable assignments for the level mvars of `r`. -/
def reconstructArgs (r : ForwardRule) (m : CompleteMatch) :
    Array (Option RPINF) × Array (Option Level) := Id.run do
  assert! m.clusterMatches.size == r.slotClusters.size
  let mut subst : Substitution := .empty r.numPremises r.numLevelParams
  for m in m.clusterMatches do
    subst := m.subst.mergeCompatible subst
  let mut args := Array.mkEmpty r.numPremises
  for i in [:r.numPremises] do
    args := args.push $ subst.find? ⟨i⟩
  let mut levels := Array.mkEmpty r.numLevelParams
  for i in [:r.numLevelParams] do
    levels := levels.push $ subst.findLevel? ⟨i⟩
  return (args, levels)

set_option linter.missingDocs false in
protected def toMessageData (r : ForwardRule) (m : CompleteMatch) :
    MessageData :=
  m!"{m.reconstructArgs r |>.1.map λ | none => m!"_" | some e => m!"{e}"}"

end CompleteMatch

namespace ForwardRuleMatch

instance : ToMessageData ForwardRuleMatch where
  toMessageData m := m!"{m.rule.name} {m.match.toMessageData m.rule}"

/-- Fold over the hypotheses contained in a match. -/
def foldHypsM [Monad M] (f : σ → FVarId → M σ) (init : σ)
    (m : ForwardRuleMatch) : M σ :=
  m.match.clusterMatches.foldlM (init := init) λ s cm =>
    cm.subst.premises.foldlM (init := s) λ
      | s, some { toExpr := e, .. } =>
        if let .fvar hyp := e.consumeMData then f s hyp else pure s
      | s, _ => pure s

/-- Fold over the hypotheses contained in a match. -/
def foldHyps (f : σ → FVarId → σ) (init : σ) (m : ForwardRuleMatch) : σ :=
  m.foldHypsM (M := Id) f init

/-- Returns `true` if any hypothesis contained in `m` satisfies `f`. -/
def anyHyp (m : ForwardRuleMatch) (f : FVarId → Bool) : Bool :=
  m.match.clusterMatches.any λ m =>
    m.subst.premises.any λ
      | some { toExpr := e, .. } =>
        if let .fvar hyp := e.consumeMData then f hyp else false
      | _ => false

/-- Get the hypotheses from the match whose types are propositions.  -/
def getPropHyps (m : ForwardRuleMatch) : MetaM (Array FVarId) :=
  m.foldHypsM (init := Array.mkEmpty m.rule.numPremises) λ hs h => do
    if ← isProof (.fvar h) then return hs.push h else return hs

/-- Construct the proof of the new hypothesis represented by `m`. -/
def getProof (goal : MVarId) (m : ForwardRuleMatch) : MetaM (Option Expr) :=
  withExceptionPrefix s!"while constructing a new hyp for forward rule {m.rule.name}:\n" do
  withConstAesopTraceNode .forward (return m!"proof construction for forward rule match") do
  goal.withContext do
  withNewMCtxDepth do
    aesop_trace[forward] "rule: {m.rule.name}"
    let e ← elabForwardRuleTerm goal m.rule.term
    let lmvars := collectLevelMVars {} e |>.result
    let eType ← instantiateMVars (← inferType e)
    aesop_trace[forward] "term: {e} : {eType}"
    let (argMVars, binderInfos, _) ← withReducible do
      forallMetaTelescope (← inferType e)
    if argMVars.size != m.rule.numPremises then
      throwError "rule term{indentExpr e}\nwith type{indentExpr eType}\n was expected to have {m.rule.numPremises} arguments, but has {argMVars.size}"
    if lmvars.size != m.rule.numLevelParams then
      throwError "rule term{indentExpr e}\nwith type{indentExpr eType}\n was expected to have {m.rule.numLevelParams} level metavariables, but has {lmvars.size}"
    let (args, levels) := m.match.reconstructArgs m.rule
    aesop_trace[forward] "args:   {args.map λ | none => m!"_" | some e => m!"{e}"}"
    aesop_trace[forward] "levels: {levels.map λ | none => m!"_" | some l => m!"{l}"}"
    for level? in levels, lmvarId in lmvars do
      if let some level := level? then
        assignLevelMVar lmvarId level
    for arg? in args, mvar in argMVars do
      if let some arg := arg? then
        mvar.mvarId!.assign arg.toExpr
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
match is for a `destruct` rule. If the `skip` function, when applied to the
normalised type of the new hypothesis, returns true, then the hypothesis is not
added to the local context. -/
def apply (goal : MVarId) (m : ForwardRuleMatch) (skip? : Option (RPINF → Bool)) :
    ScriptT BaseM (Option (MVarId × FVarId × Array FVarId)) :=
  withConstAesopTraceNode .forward (return m!"apply complete match") do
  goal.withContext do
    let name ← getUnusedUserName forwardHypPrefix
    let some prf ← m.getProof goal
      | return none
    let type ← inferType prf
    if let some skip := skip? then
      let doSkip ← withConstAesopTraceNode .forwardDebug (return m!"check whether hyp already exists") do
        let result := skip (← rpinf type)
        aesop_trace[forwardDebug] "already exists: {result}"
        pure result
      if doSkip then
        return none
    let hyp := { userName := name, value := prf, type }
    let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
      | unreachable!
    if ! m.rule.destruct then
      return some (goal, hyp, #[])
    let usedPropHyps ← goal.withContext $ m.getPropHyps
    let (goal, _) ← tryClearManyS goal usedPropHyps
    return some (goal, hyp, usedPropHyps)

end ForwardRuleMatch

private def forwardRuleMatchesToRules? (ms : Array ForwardRuleMatch)
    (mkExtra? : ForwardRuleMatch → Option α) :
    Option (Array (Rule α)) := Id.run do
  let mut ruleMap : Std.HashMap RuleName (Array ForwardRuleMatch) := ∅
  for m in ms do
    let name := m.rule.name
    if let some ms := ruleMap[name]? then
      ruleMap := ruleMap.insert name (ms.push m)
    else
      ruleMap := ruleMap.insert name #[m]
  let mut result := Array.mkEmpty ruleMap.size
  for (name, ms) in ruleMap do
    let some extra := mkExtra? ms[0]!
      | return none
    result := result.push {
      indexingMode := .unindexed
      pattern? := none
      tac := .forwardMatches ms
      name, extra
    }
  return some result

/-- Convert forward rule matches to norm rules. Fails if any of the matches is
not a norm rule match.  -/
def forwardRuleMatchesToNormRules? (ms : Array ForwardRuleMatch) :
    Option (Array NormRule) :=
  forwardRuleMatchesToRules? ms
    (·.rule.prio.penalty?.map ({ penalty := · }))

/-- Convert forward rule matches to safe rules. Fails if any of the matches is
not a safe rule match. -/
def forwardRuleMatchesToSafeRules? (ms : Array ForwardRuleMatch) :
    Option (Array SafeRule) :=
  forwardRuleMatchesToRules? ms
    (·.rule.prio.penalty?.map ({ penalty := ·, safety := .safe }))

/-- Convert forward rule matches to unsafe rules. Fails if any of the matches
is not an unsafe rule match. -/
def forwardRuleMatchesToUnsafeRules? (ms : Array ForwardRuleMatch) :
    Option (Array UnsafeRule) :=
  forwardRuleMatchesToRules? ms
    (·.rule.prio.successProbability?.map ({ successProbability := · }))

end Aesop
