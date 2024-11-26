/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.Match
import Aesop.RuleTac.Basic
import Aesop.RuleTac.ElabRuleTerm
import Aesop.RuleTac.Forward.Basic
import Aesop.Script.SpecificTactics
import Batteries.Lean.Meta.UnusedNames

open Lean
open Lean.Meta

namespace Aesop.RuleTac

partial def makeForwardHyps (e : Expr) (pat? : Option RulePattern)
    (patInst : RulePatternInstantiation)
    (immediate : UnorderedArraySet PremiseIndex) (maxDepth? : Option Nat)
    (forwardHypData : ForwardHypData) :
    MetaM (Array (Expr × Nat) × Array FVarId) :=
  withNewMCtxDepth (allowLevelAssignments := true) do
    let type ← inferType e
    let patAndInst? := pat?.map (·, patInst)
    let (argMVars, binderInfos, _, patInstantiatedMVars) ←
      openRuleType patAndInst? type
    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for h : i in [:argMVars.size] do
      let mvarId := argMVars[i]'h.2 |>.mvarId!
      if patInstantiatedMVars.contains mvarId then
        continue
      if immediate.contains ⟨i⟩ then
        immediateMVars := immediateMVars.push mvarId
      else if binderInfos[i]!.isInstImplicit then
        instMVars := instMVars.push mvarId
    let (proofs, usedHyps, _) ←
      loop app instMVars immediateMVars 0 #[] 0 #[] #[] ∅
    return (proofs, usedHyps)
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (proofsAcc : Array (Expr × Nat)) (currentMaxHypDepth : Nat)
        (currentUsedHyps : Array FVarId) (usedHypsAcc : Array FVarId)
        (proofTypesAcc : Std.HashSet Expr) :
        MetaM (Array (Expr × Nat) × Array FVarId × Std.HashSet Expr) := do
      if h : i < immediateMVars.size then
        let mvarId := immediateMVars.get ⟨i, h⟩
        let type ← mvarId.getType
        (← getLCtx).foldlM (init := (proofsAcc, usedHypsAcc, proofTypesAcc)) λ s@(proofsAcc, usedHypsAcc, proofTypesAcc) ldecl => do
          if ldecl.isImplementationDetail then
            return s
          let hypDepth := forwardHypData.depths.getD ldecl.fvarId 0
          let currentMaxHypDepth := max currentMaxHypDepth hypDepth
          if let some maxDepth := maxDepth? then
            if currentMaxHypDepth + 1 > maxDepth then
              return s
          withoutModifyingState do
            if ← isDefEq ldecl.type type then
              mvarId.assign (mkFVar ldecl.fvarId)
              let currentUsedHyps := currentUsedHyps.push ldecl.fvarId
              loop app instMVars immediateMVars (i + 1) proofsAcc
                currentMaxHypDepth currentUsedHyps usedHypsAcc proofTypesAcc
            else
              return s
      else
        for instMVar in instMVars do
          instMVar.withContext do
            let inst ← synthInstance (← instMVar.getType)
            instMVar.assign inst
        let proof := (← abstractMVars app).expr
        let type ← instantiateMVars (← inferType proof)
        let redundant ←
          pure (proofTypesAcc.contains type) <||>
          forwardHypData.containsTypeUpToIds type
        if redundant then
          return (proofsAcc, usedHypsAcc, proofTypesAcc)
        else
          let depth := currentMaxHypDepth + 1
          let proofsAcc := proofsAcc.push (proof, depth)
          let proofTypesAcc := proofTypesAcc.insert type
          let usedHypsAcc := usedHypsAcc ++ currentUsedHyps
          return (proofsAcc, usedHypsAcc, proofTypesAcc)

def assertForwardHyp (goal : MVarId) (hyp : Hypothesis) (depth : Nat) :
    ScriptM (FVarId × MVarId) := do
  withScriptStep goal (λ (_, g) => #[g]) (λ _ => true) tacticBuilder do
  withReducible do
    let hyp := {
      hyp with
      binderInfo := .default
      kind := .default
    }
    let implDetailHyp := {
        hyp with
        userName := forwardImplDetailHypName hyp.userName depth
        binderInfo := .default
        kind := .implDetail
    }
    let (#[fvarId, _], goal) ← goal.assertHypotheses #[hyp, implDetailHyp]
      | throwError "aesop: internal error in assertForwardHyp: unexpected number of asserted fvars"
    return (fvarId, goal)
where
  tacticBuilder _ := Script.TacticBuilder.assertHypothesis goal hyp .reducible

def applyForwardRule (goal : MVarId) (e : Expr) (pat? : Option RulePattern)
    (patInsts : Std.HashSet RulePatternInstantiation)
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool)
    (maxDepth? : Option Nat) : ScriptM Subgoal :=
  withReducible $ goal.withContext do
    let initialGoal := goal
    let forwardHypData ← getForwardHypData
    let mut newHypProofs := #[]
    let mut usedHyps := ∅
    if pat?.isSome then
      for patInst in patInsts do
        let (newHypProofs', usedHyps') ←
          makeForwardHyps e pat? patInst immediate maxDepth? forwardHypData
        newHypProofs := newHypProofs ++ newHypProofs'
        usedHyps := usedHyps ++ usedHyps'
    else
      let (newHypProofs', usedHyps') ←
        makeForwardHyps e pat? .empty immediate maxDepth? forwardHypData
      newHypProofs := newHypProofs'
      usedHyps := usedHyps'
    usedHyps :=
      usedHyps.sortDedup (ord := ⟨λ x y => x.name.quickCmp y.name⟩)
    if newHypProofs.isEmpty then
      err
    let newHypUserNames ← getUnusedUserNames newHypProofs.size forwardHypPrefix
    let mut newHyps := #[]
    for (proof, depth) in newHypProofs, userName in newHypUserNames do
      let type ← inferType proof
      newHyps := newHyps.push ({ value := proof, type, userName }, depth)
    let mut goal := goal
    let mut addedFVars := ∅
    for (newHyp, depth) in newHyps do
      let (fvarId, goal') ← assertForwardHyp goal newHyp depth
      goal := goal'
      addedFVars := addedFVars.insert fvarId
    let mut diff := {
      oldGoal := initialGoal
      newGoal := goal
      addedFVars
      removedFVars := ∅
      targetMaybeChanged := false
    }
    if clear then
      let usedPropHyps ← goal.withContext do
        usedHyps.filterM λ fvarId => isProof (.fvar fvarId)
      let (goal', removedFVars) ← tryClearManyS goal usedPropHyps
      let removedFVars := removedFVars.foldl (init := ∅) λ set fvarId =>
        set.insert fvarId
      goal := goal'
      diff := { diff with newGoal := goal, removedFVars }
    return { diff }
  where
    err {α} : MetaM α := throwError
      "found no instances of {e} (other than possibly those which had been previously added by forward rules)"

@[inline]
def forwardExpr (e : Expr) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => input.goal.withContext do
    let (goal, steps) ←
      applyForwardRule input.goal e pat? input.patternInstantiations immediate
        (clear := clear) input.options.forwardMaxDepth? |>.run
    return (#[goal], steps, none)

def forwardConst (decl : Name) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool) :
    RuleTac := λ input => do
  let e ← mkConstWithFreshMVarLevels decl
  forwardExpr e pat? immediate (clear := clear) input

def forwardTerm (stx : Term) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool) :
    RuleTac := λ input =>
  input.goal.withContext do
    let e ← elabRuleTermForApplyLikeMetaM input.goal stx
    forwardExpr e pat? immediate (clear := clear) input

def forward (t : RuleTerm) (pat? : Option RulePattern)
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool) : RuleTac :=
  match t with
  | .const decl => forwardConst decl pat? immediate clear
  | .term tm => forwardTerm tm pat? immediate clear

def forwardMatch (m : ForwardRuleMatch) :
    RuleTac := SingleRuleTac.toRuleTac λ input => do
  let (some (goal, hyp, removedFVars), steps) ←
    m.apply input.goal (skipExisting := true) |>.run
    | throwError "hyp already exists or synthesis of instance arguments failed"
  let diff := {
    oldGoal := input.goal
    newGoal := goal
    addedFVars := {hyp}
    targetMaybeChanged := false
    removedFVars := .ofArray removedFVars
  }
  return (#[{ diff }], some steps, none)

end Aesop.RuleTac
