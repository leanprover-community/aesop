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

/--
The level of a match `m` is the greatest slot index `i` such that `m` associates
a hypothesis to slot `i`.
-/
def level (m : Match) : SlotIndex :=
  ⟨m.revHyps.length - 1⟩

end Match

namespace CompleteMatch

/-- Given a complete match `m` for `r`, get arguments to `r` contained in the
match's slots and substitution. -/
def reconstructArgs (r : ForwardRule) (m : CompleteMatch) :
    Array Expr := Id.run do
  let mut slotHyps : Std.HashMap PremiseIndex FVarId := ∅
  for h : i in [:r.slotClusters.size] do
    let cluster := r.slotClusters[i]
    let some m := m.clusterMatches[i]?
      | panic! s!"match for rule {r.name} is not complete: no cluster match for cluster {i}"
    let hyps := m.revHyps.toArray.reverse
    for h' : j in [:cluster.size] do
      let slot := cluster[j]
      let some hyp := hyps[j]?
        | panic! s!"match for rule {r.name} is not complete: no hyp for slot with premise index {slot.premiseIndex} in cluster {i}"
      slotHyps := slotHyps.insert slot.premiseIndex hyp

  let mut subst : Substitution := .empty r.numPremiseIndexes
  for m in m.clusterMatches do
    subst := subst.mergeCompatible m.subst

  let mut args := Array.mkEmpty r.numPremises
  for i in [:r.numPremises] do
    if let some hyp := slotHyps.get? ⟨i⟩ then
      args := args.push (.fvar hyp)
    else if let some inst := subst.find? ⟨i⟩ then
      args := args.push inst
    else
      panic! s!"match for rule {r.name} is not complete: no hyp or instantiation for premise {i}"

  return args

end CompleteMatch

namespace ForwardRuleMatch

/-- Compare two queue entries by rule priority and rule name. Higher-priority
rules are considered less (since the queues are min-queues). -/
protected def le (m₁ m₂ : ForwardRuleMatch) : Bool :=
  m₁.rule.prio.le m₂.rule.prio ||
  (m₁.rule.prio == m₂.rule.prio && (m₁.rule.name.compare m₂.rule.name).isLE)

/-- Fold over the hypotheses contained in a match. -/
def foldHyps (f : σ → FVarId → σ) (init : σ) (m : ForwardRuleMatch) : σ :=
  m.match.clusterMatches.foldl (init := init) λ s cm =>
    cm.revHyps.foldl (init := s) f

/-- Returns `true` if any hypothesis contained in `m` satisfies `f`. -/
def anyHyp (m : ForwardRuleMatch) (f : FVarId → Bool) : Bool :=
  m.match.clusterMatches.any (·.revHyps.any f)

/-- Construct the proof of the new hypothesis represented by `m`. -/
def getProof (goal : MVarId) (m : ForwardRuleMatch) : MetaM Expr :=
  withConstAesopTraceNode .forward (return m!"proof construction for forward rule match") do
  goal.withContext do
  withNewMCtxDepth do
    aesop_trace[forward] "rule: {m.rule.name}"
    let e ← elabForwardRuleTerm goal m.rule.term
    aesop_trace[forward] "term: {e} : {← inferType e}"
    let (argMVars, _, _) ← forallMetaTelescope (← inferType e)
    let args := m.match.reconstructArgs m.rule
    aesop_trace[forward] "args: {args}"
    for arg in args, mvar in argMVars do
      if ! (← isDefEq arg mvar) then
        throwError "type mismatch during reconstruction of match for forward rule{indentD m!"{m.rule.name}"}\n: expected{indentExpr (← inferType mvar)}\nbut got{indentExpr arg} : {← inferType arg}"
    let result ← instantiateMVars $ mkAppN e argMVars
    if ← hasAssignableMVar result then
      -- NOTE This prevents applications of forward rules where a universe
      -- param occurs only in the codomain.
      throwError "reconstruction of complete match for forward rule{indentD m!"{m.rule.name}"}\nhas mvars:{indentExpr result}"
    aesop_trace[forward] "result: {result}"
    return result

/-- Apply a forward rule match to a goal. This adds the hypothesis corresponding
to the match to the local context. -/
def apply (goal : MVarId) (m : ForwardRuleMatch) : ScriptM (MVarId × FVarId) :=
  goal.withContext do
    let name ← getUnusedUserName forwardHypPrefix
    let prf ← m.getProof goal
    let type ← inferType prf
    let hyp := { userName := name, value := prf, type }
    let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
      | unreachable!
    return (goal, hyp)

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
