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

partial def makeForwardHyps (e : Expr) (patSubst? : Option Substitution)
    (immediate : UnorderedArraySet PremiseIndex) (maxDepth? : Option Nat)
    (forwardHypData : ForwardHypData) (existingHypTypes : PHashSet RPINF) :
    BaseM (Array (Expr × Nat) × Array FVarId) :=
  withNewMCtxDepth (allowLevelAssignments := true) do
    let type ← inferType e
    let (argMVars, binderInfos, _) ← openRuleType patSubst? e
    let app := mkAppN e (argMVars.map .mvar)
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for h : i in [:argMVars.size] do
      let mvarId := argMVars[i]
      if ← mvarId.isAssignedOrDelayedAssigned then
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
        (proofTypesAcc : Std.HashSet RPINF) :
        BaseM (Array (Expr × Nat) × Array FVarId × Std.HashSet RPINF) := do
      if h : immediateMVars.size > 0 ∧ i < immediateMVars.size then
        -- We go through the immediate mvars back to front. This is more
        -- efficient because assigning later mvars may already determine the
        -- assignments of earlier mvars.
        let mvarId := immediateMVars[immediateMVars.size - 1 - i]
        if ← mvarId.isAssignedOrDelayedAssigned then
          -- If the mvar is already assigned, we still need to update and check
          -- the hyp depth.
          let mut currentMaxHypDepth := currentMaxHypDepth
          let (_, fvarIds) ← (← instantiateMVars (.mvar mvarId)).collectFVars |>.run {}
          for fvarId in fvarIds.fvarIds do
            let hypDepth := forwardHypData.depths.getD fvarId 0
            currentMaxHypDepth := max currentMaxHypDepth hypDepth
          if let some maxDepth := maxDepth? then
            if currentMaxHypDepth + 1 > maxDepth then
              return (proofsAcc, usedHypsAcc, proofTypesAcc)
          return ← loop app instMVars immediateMVars (i + 1) proofsAcc
            currentMaxHypDepth currentUsedHyps usedHypsAcc proofTypesAcc
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
        let type ← rpinf (← inferType proof)
        let redundant :=
          proofTypesAcc.contains type || existingHypTypes.contains type
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

def applyForwardRule (goal : MVarId) (e : Expr)
    (patSubsts? : Option (Std.HashSet Substitution))
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool)
    (maxDepth? : Option Nat) (existingHypTypes : PHashSet RPINF) :
    ScriptM Subgoal :=
  withReducible $ goal.withContext do
    let initialGoal := goal
    let forwardHypData ← getForwardHypData
    let mut newHypProofs := #[]
    let mut usedHyps := ∅
    if let some patSubsts := patSubsts? then
      for patSubst in patSubsts do
        let (newHypProofs', usedHyps') ←
          makeForwardHyps e patSubst immediate maxDepth? forwardHypData
            existingHypTypes
        newHypProofs := newHypProofs ++ newHypProofs'
        usedHyps := usedHyps ++ usedHyps'
    else
      let (newHypProofs', usedHyps') ←
        makeForwardHyps e none immediate maxDepth? forwardHypData
          existingHypTypes
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
      targetChanged := .false
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
def forwardExpr (e : Expr) (immediate : UnorderedArraySet PremiseIndex)
    (clear : Bool) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => input.goal.withContext do
    let (goal, steps) ←
      applyForwardRule input.goal e input.patternSubsts? immediate
        (clear := clear) input.options.forwardMaxDepth? input.hypTypes
      |>.run
    return (#[goal], steps, none)

def forwardConst (decl : Name) (immediate : UnorderedArraySet PremiseIndex)
    (clear : Bool) : RuleTac := λ input => do
  let e ← mkConstWithFreshMVarLevels decl
  forwardExpr e immediate (clear := clear) input

def forwardTerm (stx : Term) (immediate : UnorderedArraySet PremiseIndex)
    (clear : Bool) : RuleTac := λ input =>
  input.goal.withContext do
    let e ← elabRuleTermForApplyLikeMetaM input.goal stx
    forwardExpr e immediate (clear := clear) input

def forward (t : RuleTerm) (immediate : UnorderedArraySet PremiseIndex)
    (clear : Bool) : RuleTac :=
  match t with
  | .const decl => forwardConst decl immediate clear
  | .term tm => forwardTerm tm immediate clear

def forwardMatches (ms : Array ForwardRuleMatch) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let skip type := input.hypTypes.contains type
    let mut goal := input.goal
    let mut addedFVars := ∅
    let mut removedFVars := ∅
    let mut anySuccess := false
    let mut steps := #[]
    for m in ms do
      let (some (goal', hyp, removedFVars'), steps') ← m.apply goal (some skip) |>.run
        | continue
      anySuccess := true
      goal := goal'
      addedFVars := addedFVars.insert hyp
      removedFVars := removedFVars.insertMany removedFVars'
      steps := steps ++ steps'
    if ! anySuccess then
      throwError "failed to add hyps for any of the following forward rule matches:{indentD $ MessageData.joinSep (ms.map toMessageData |>.toList) "\n"}"
    let diff := {
      oldGoal := input.goal
      newGoal := goal
      targetChanged := .false
      addedFVars, removedFVars
    }
    return (#[{ diff }], some steps, none)

def forwardMatch (m : ForwardRuleMatch) : RuleTac :=
  .forwardMatches #[m]

end Aesop.RuleTac
