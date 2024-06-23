/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic
import Aesop.RuleTac.ElabRuleTerm
import Batteries.Lean.Meta.UnusedNames
import Batteries.Lean.Meta.AssertHypotheses
import Aesop.Script.SpecificTactics
import Aesop.RuleTac.Forward.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleTac

partial def makeForwardHyps (e : Expr) (pat? : Option RulePattern)
    (patInst : RulePatternInstantiation) (immediate : UnorderedArraySet Nat) :
    MetaM (Array Expr × Array FVarId) :=
  withNewMCtxDepth (allowLevelAssignments := true) do
    let type ← inferType e
    let (argMVars, binderInfos, patInstantiatedMVars) ←
      if let some pat := pat? then
        let (argMVars, binderInfos, _, patInstantiatedMVars) ←
          pat.openRuleType patInst type
        pure (argMVars, binderInfos, patInstantiatedMVars)
      else
        let (argMVars, binderInfos, _) ← forallMetaTelescopeReducing type
        pure (argMVars, binderInfos, ∅)
    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for h : i in [:argMVars.size] do
      let mvarId := argMVars[i]'h.2 |>.mvarId!
      if patInstantiatedMVars.contains mvarId then
        continue
      if immediate.contains i then
        immediateMVars := immediateMVars.push mvarId
      else if binderInfos[i]!.isInstImplicit then
        instMVars := instMVars.push mvarId
    loop app instMVars immediateMVars 0 #[] #[] #[]
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (proofsAcc : Array Expr) (currentUsedHyps : Array FVarId)
        (usedHypsAcc : Array FVarId) : MetaM (Array Expr × Array FVarId) := do
      if h : i < immediateMVars.size then
        let mvarId := immediateMVars.get ⟨i, h⟩
        let type ← mvarId.getType
        (← getLCtx).foldlM (init := (proofsAcc, usedHypsAcc)) λ s@(proofsAcc, usedHypsAcc) ldecl =>
          if ldecl.isImplementationDetail then
            pure s
          else
            withoutModifyingState do
              if ← isDefEq ldecl.type type then
                mvarId.assign (mkFVar ldecl.fvarId)
                let currentUsedHyps := currentUsedHyps.push ldecl.fvarId
                loop app instMVars immediateMVars (i + 1) proofsAcc
                  currentUsedHyps usedHypsAcc
              else
                pure s
      else
        for instMVar in instMVars do
          instMVar.withContext do
            let inst ← synthInstance (← instMVar.getType)
            instMVar.assign inst
        let proof := (← abstractMVars app).expr
        let proofsAcc := proofsAcc.push proof
        let usedHypsAcc := usedHypsAcc ++ currentUsedHyps
        return (proofsAcc, usedHypsAcc)

def isForwardImplDetailHyp (ldecl : LocalDecl) : Bool :=
  ldecl.isImplementationDetail && isForwardImplDetailHypName ldecl.userName

def getForwardImplDetailHyps : MetaM (Array LocalDecl) := do
 let mut result := #[]
 for ldecl in ← getLCtx do
    if isForwardImplDetailHyp ldecl then
      result := result.push ldecl
  return result

def getForwardHypTypes : MetaM (HashSet Expr) := do
  let ldecls ← getForwardImplDetailHyps
  return ldecls.foldl (init := ∅) λ result ldecl => result.insert ldecl.type

def _root_.Aesop.clearForwardImplDetailHyps (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let hyps ← getForwardImplDetailHyps
    goal.tryClearMany $ hyps.map (·.fvarId)

def assertForwardHyp (goal : MVarId) (hyp : Hypothesis) (md : TransparencyMode) :
    ScriptM MVarId := do
  withScriptStep goal (#[·]) (λ _ => true) tacticBuilder do
  withTransparency md do
    let hyp := {
      hyp with
      binderInfo := .default
      kind := .default
    }
    let implDetailHyp := {
        hyp with
        userName := forwardImplDetailHypName hyp.userName 0 -- TODO depth
        binderInfo := .default
        kind := .implDetail
    }
    (·.snd) <$> goal.assertHypotheses' #[hyp, implDetailHyp]
where
  tacticBuilder _ := Script.TacticBuilder.assertHypothesis goal hyp md

def applyForwardRule (goal : MVarId) (e : Expr) (pat? : Option RulePattern)
    (patInsts : HashSet RulePatternInstantiation)
    (immediate : UnorderedArraySet Nat) (clear : Bool)
    (md : TransparencyMode) : ScriptM MVarId :=
  withTransparency md $ goal.withContext do
    let mut newHypProofs := #[]
    let mut usedHyps := ∅
    if pat?.isSome then
      for patInst in patInsts do
        let (newHypProofs', usedHyps') ←
          makeForwardHyps e pat? patInst immediate
        newHypProofs := newHypProofs ++ newHypProofs'
        usedHyps := usedHyps ++ usedHyps'
    else
      let (newHypProofs', usedHyps') ← makeForwardHyps e pat? .empty immediate
      newHypProofs := newHypProofs'
      usedHyps := usedHyps'
    usedHyps :=
      usedHyps.sortDedup (ord := ⟨λ x y => x.name.quickCmp y.name⟩)
    if newHypProofs.isEmpty then
      err
    let forwardHypTypes ← getForwardHypTypes
    let mut newHyps' := Array.mkEmpty newHypProofs.size
    let mut newHypTypes : HashSet Expr := {}
    for proof in newHypProofs do
      let type ← inferType proof
      if forwardHypTypes.contains type || newHypTypes.contains type then
        continue
      newHypTypes := newHypTypes.insert type
      newHyps' := newHyps'.push (proof, type)
    if newHyps'.isEmpty then
      err
    let newHypUserNames ← getUnusedUserNames newHyps'.size forwardHypPrefix
    let newHyps := newHyps'.zipWith newHypUserNames λ (proof, type) userName =>
      { value := proof, type, userName }
    let mut goal := goal
    for newHyp in newHyps do
      goal ← assertForwardHyp goal newHyp md
    if clear then
      let (goal', _) ← tryClearManyS goal usedHyps
      goal := goal'
    return goal
  where
    err {α} : MetaM α := throwError
      "found no instances of {e} (other than possibly those which had been previously added by forward rules)"

@[inline]
def forwardExpr (e : Expr) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet Nat) (clear : Bool) (md : TransparencyMode) :
    RuleTac :=
  SingleRuleTac.toRuleTac λ input => input.goal.withContext do
    let (goal, steps) ←
      applyForwardRule input.goal e pat? input.patternInstantiations immediate
        (clear := clear) md |>.run
    return (#[goal], steps, none)

def forwardConst (decl : Name) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet Nat) (clear : Bool) (md : TransparencyMode) :
    RuleTac := λ input => do
  forwardExpr (← mkConstWithFreshMVarLevels decl) pat? immediate clear md input

def forwardTerm (stx : Term) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet Nat) (clear : Bool) (md : TransparencyMode) :
    RuleTac := λ input =>
  input.goal.withContext do
    let e ← elabRuleTermForApplyLikeMetaM input.goal stx
    forwardExpr e pat? immediate (clear := clear) md input

end Aesop.RuleTac
