/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Forward.Match
public import Aesop.RuleTac.Basic
public import Aesop.RuleTac.ElabRuleTerm
public import Aesop.RuleTac.Forward.Basic
public import Aesop.Script.SpecificTactics
public import Batteries.Lean.Meta.UnusedNames

public section

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop.RuleTac

structure ForwardM.Context where
  maxDepth? : Option Nat
  forwardHypData : ForwardHypData
  deriving Inhabited

structure ForwardM.State where
  toAssert : Array (Expr × Expr × Nat) := #[]
  usedHyps : Std.HashSet FVarId := ∅
  deriving Inhabited

abbrev ForwardM := ReaderT ForwardM.Context <| StateRefT ForwardM.State ScriptM

partial def makeForwardHypProofs (e : Expr) (patSubst? : Option Substitution)
    (immediate : UnorderedArraySet PremiseIndex) : ForwardM Unit :=
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
    loop app instMVars immediateMVars 0 0 #[]
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (currentMaxHypDepth : Nat) (currentUsedHyps : Array FVarId) :
        ForwardM Unit := do
      if h : immediateMVars.size > 0 ∧ i < immediateMVars.size then
        -- We go through the immediate mvars back to front. This is more
        -- efficient because assigning later mvars may already determine the
        -- assignments of earlier mvars.
        let mvarId := immediateMVars[immediateMVars.size - 1 - i]
        if ← mvarId.isAssignedOrDelayedAssigned then
          -- If the mvar is already assigned, we still need to update and check
          -- the hyp depth.
          let mut currentMaxHypDepth := currentMaxHypDepth
          let (_, fvarIds) ← (Expr.mvar mvarId).collectFVars |>.run {}
          for fvarId in fvarIds.fvarIds do
            let hypDepth := (← read).forwardHypData.depths.getD fvarId 0
            currentMaxHypDepth := max currentMaxHypDepth hypDepth
          if let some maxDepth := (← read).maxDepth? then
            if currentMaxHypDepth + 1 > maxDepth then
              return
          return ← loop app instMVars immediateMVars (i + 1) currentMaxHypDepth
                     currentUsedHyps
        let type ← mvarId.getType
        for ldecl in ← getLCtx do
          if ldecl.isImplementationDetail then
            continue
          let hypDepth := (← read).forwardHypData.depths.getD ldecl.fvarId 0
          let currentMaxHypDepth := max currentMaxHypDepth hypDepth
          if let some maxDepth := (← read).maxDepth? then
            if currentMaxHypDepth + 1 > maxDepth then
              continue
          let metaState ← show MetaM _ from saveState
          try
            if ← isDefEq ldecl.type type then
              mvarId.assign (mkFVar ldecl.fvarId)
              let currentUsedHyps := currentUsedHyps.push ldecl.fvarId
              loop app instMVars immediateMVars (i + 1)
                currentMaxHypDepth currentUsedHyps
          finally
            metaState.restore
      else
        for instMVar in instMVars do
          try
            instMVar.assign <| ← instMVar.withContext do synthInstance (← instMVar.getType)
          catch e =>
            trace[saturate] "failed to synthesize{indentExpr (← instMVar.getType)}"
            return
        let proof := (← abstractMVars app).expr
        let type ← inferType proof
        if ! (← isRedundant type) then
          let depth := currentMaxHypDepth + 1
          modify fun s => {
            toAssert := s.toAssert.push (proof, type, depth)
            usedHyps := s.usedHyps.insertMany currentUsedHyps
          }

    isRedundant (type : Expr) : ForwardM Bool := do
      (← get).toAssert.anyM (isDefEqReducibleRigid ·.1 type) <||>
      isHypRedundantReducibleRigid type

def makeForwardHypProofs' (e : Expr)
    (patSubsts? : Option (Array Substitution))
    (immediate : UnorderedArraySet PremiseIndex) : ForwardM Unit := do
  if let some patSubsts := patSubsts? then
    for patSubst in patSubsts do
      makeForwardHypProofs e patSubst immediate
  else
    makeForwardHypProofs e none immediate

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
    (patSubsts? : Option (Array Substitution))
    (immediate : UnorderedArraySet PremiseIndex) (clear : Bool)
    (maxDepth? : Option Nat) :
    ScriptM Subgoal :=
  withReducible do goal.withContext do
    let initialGoal := goal
    let (_, { toAssert, usedHyps }) ←
      makeForwardHypProofs' e patSubsts? immediate
        |>.run { maxDepth?, forwardHypData := ← getForwardHypData } |>.run {}
    if toAssert.isEmpty then
      throwError "found no instances of {e} (other than possibly those which had been previously added by forward rules)"
    let mut goal := goal
    let mut addedFVars := ∅
    let userNames ← getUnusedUserNames toAssert.size forwardHypPrefix
    for (value, type, depth) in toAssert, userName in userNames do
      let (fvarId, mvarId) ← assertForwardHyp goal { userName, type, value } depth
      goal := mvarId
      addedFVars := addedFVars.insert fvarId
    let mut diff := {
      oldGoal := initialGoal
      newGoal := goal
      removedFVars := ∅
      targetChanged := false
      addedFVars
    }
    if clear then
      let usedPropHyps ← goal.withContext do
        usedHyps.toArray.filterM λ fvarId => isProof (.fvar fvarId)
      let (goal', removedFVars) ← tryClearManyS goal usedPropHyps
      let removedFVars := removedFVars.foldl (init := ∅) λ set fvarId =>
        set.insert fvarId
      goal := goal'
      diff := { diff with newGoal := goal, removedFVars }
    return { diff }

@[inline]
def forwardExpr (e : Expr) (immediate : UnorderedArraySet PremiseIndex)
    (clear : Bool) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => input.goal.withContext do
    let (goal, steps) ←
      applyForwardRule input.goal e input.patternSubsts? immediate
        (clear := clear) input.options.forwardMaxDepth?
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
    let mut goal := input.goal
    let mut addedFVars := ∅
    let mut removedFVars := ∅
    let mut anySuccess := false
    let mut steps := #[]
    for m in ms do
      let (some (goal', hyp, removedFVars'), steps') ←
        m.apply goal (skipExistingProps := true) |>.run
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
