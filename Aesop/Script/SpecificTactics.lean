/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Tactic
import Aesop.Util.Tactic.Ext
import Aesop.Util.Tactic.Unfold
import Aesop.Script.CtorNames
import Aesop.Script.ScriptM
import Batteries.Lean.Meta.Inaccessible

open Lean
open Lean.Meta
open Lean.PrettyPrinter (delab)

namespace Aesop.Script

def Tactic.skip : Tactic :=
  .unstructured $ Unhygienic.run `(tactic| skip)

namespace TacticBuilder

def applyStx (e : Term) (md : TransparencyMode) : TacticBuilder := do
  let tac := withAllTransparencySyntax md (← `(tactic| apply $e))
  return .unstructured tac

def apply (mvarId : MVarId) (e : Expr) (md : TransparencyMode) :
    TacticBuilder := do
  let e ← mvarId.withContext $ delab e
  let tac := withAllTransparencySyntax md (← `(tactic| apply $e))
  return .unstructured tac

def exactFVar (goal : MVarId) (fvarId : FVarId) (md : TransparencyMode) :
    TacticBuilder := do
  let ident := mkIdent (← goal.withContext $ fvarId.getUserName)
  let tac := withAllTransparencySyntax md $ ← `(tactic| exact $ident)
  return .unstructured tac

def replace (preGoal postGoal : MVarId) (fvarId : FVarId) (type : Expr)
    (proof : Expr) : TacticBuilder := do
  let userName ← preGoal.withContext $ fvarId.getUserName
  let proof ← preGoal.withContext $ delab proof
  let type ← postGoal.withContext $ delab type
  let tac ← `(tactic| replace $(mkIdent userName) : $type := $proof)
  return .unstructured tac

def assertHypothesis (goal : MVarId) (h : Hypothesis) (md : TransparencyMode) :
    TacticBuilder :=
  goal.withContext do
    let tac ← `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))
    return .unstructured $ withAllTransparencySyntax md tac

def clear (goal : MVarId) (fvarIds : Array FVarId) : TacticBuilder :=
  goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    return .unstructured $ ← `(tactic| clear $userNames*)

def cases (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder := do
  goal.withContext do
    let rcasesPat := ctorNamesToRCasesPats ctorNames
    let e ← delab e
    let uTactic ← `(tactic| rcases $e:term with $rcasesPat)
    let sTactic := {
      numSubgoals := ctorNames.size
      run := λ conts =>
        Unhygienic.run do
          let alts := ctorNamesToInductionAlts (ctorNames.zip conts)
          `(tactic| cases $e:term $alts:inductionAlts)
    }
    return .structured uTactic sTactic

def obtain (goal : MVarId) (e : Expr) (ctorNames : CtorNames) : TacticBuilder :=
  goal.withContext do
    let tac ← `(tactic| obtain $(ctorNames.toRCasesPat) := $(← delab e))
    return .unstructured tac

def casesOrObtain (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder :=
  if h : ctorNames.size = 1 then
    obtain goal e ctorNames[0]
  else
    cases goal e ctorNames

def renameInaccessibleFVars (postGoal : MVarId) (renamedFVars : Array FVarId) :
    TacticBuilder :=
  if renamedFVars.isEmpty then
    return .skip
  else
    postGoal.withContext do
      let ids ← renamedFVars.mapM λ fvarId => do
        let userName := mkIdent (← fvarId.getDecl).userName
        `(binderIdent| $userName:ident)
      return .unstructured $ ← `(tactic| rename_i $ids:binderIdent*)

def unfold (usedDecls : Array Name) (aesopUnfold : Bool) : TacticBuilder := do
  let usedDecls := usedDecls.map mkIdent
  let tac ←
  if aesopUnfold then
    `(tactic | aesop_unfold $usedDecls:ident*)
  else
    `(tactic | unfold $usedDecls:ident*)
  return .unstructured tac

def unfoldAt (goal : MVarId) (fvarId : FVarId) (usedDecls : Array Name)
    (aesopUnfold : Bool) : TacticBuilder :=
  goal.withContext do
    let hypIdent := mkIdent (← goal.withContext $ fvarId.getUserName)
    let usedDecls := usedDecls.map mkIdent
    let tac ←
    if aesopUnfold then
      `(tactic| aesop_unfold $usedDecls:ident* at $hypIdent:ident)
    else
      `(tactic| unfold $usedDecls:ident* at $hypIdent:ident)
    return .unstructured tac

open Lean.Parser.Tactic in
def extN (r : ExtResult) : TacticBuilder := do
  if r.depth == 0 then
    return .skip
  let mut pats := #[]
  if h : 0 < r.goals.size then
    let pats' ← r.goals[0].1.withContext do r.commonFVarIds.mapM mkPat
    pats := pats ++ pats'
    for (g, fvarIds) in r.goals do
      let pats' ← g.withContext do fvarIds.mapM mkPat
      pats := pats ++ pats'
  let depthStx := Syntax.mkNumLit $ toString r.depth
  let tac ← `(tactic| ext $pats:rintroPat* : $depthStx)
  return .unstructured tac
where
  mkPat (fvarId : FVarId) : MetaM (TSyntax `rintroPat) := do
    `(rintroPat| $(mkIdent $ ← fvarId.getUserName):ident)

private def simpAllOrSimpAtStarStx [Monad m] [MonadQuotation m] (simpAll : Bool)
    (configStx? : Option Term) : m (Syntax.Tactic) :=
  if simpAll then
    match configStx? with
    | none => `(tactic| simp_all)
    | some cfg => `(tactic| simp_all (config := $cfg))
  else
    match configStx? with
    | none => `(tactic| simp at *)
    | some cfg => `(tactic| simp (config := $cfg) at *)

private def simpAllOrSimpAtStarOnlyStx (simpAll : Bool) (inGoal : MVarId)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    MetaM Syntax.Tactic := do
  let originalStx ← simpAllOrSimpAtStarStx simpAll configStx?
  let stx ← inGoal.withContext do
    Elab.Tactic.mkSimpOnly originalStx usedTheorems
  return ⟨stx⟩

def simpAllOrSimpAtStarOnly (simpAll : Bool) (inGoal : MVarId)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    TacticBuilder :=
  .unstructured <$>
    simpAllOrSimpAtStarOnlyStx simpAll inGoal configStx? usedTheorems

private def isGlobalSimpTheorem (thms : SimpTheorems) (simprocs : Simprocs) : Origin → Bool
  | origin@(.decl decl) =>
    simprocs.simprocNames.contains decl ||
    thms.lemmaNames.contains origin ||
    thms.toUnfold.contains decl ||
    thms.toUnfoldThms.contains decl
  | _ => false

def simpAllOrSimpAtStar (simpAll : Bool) (inGoal : MVarId)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    TacticBuilder := do
  let simpTheorems ← getSimpTheorems
  let simprocs ← Simp.getSimprocs
  let (map, size) ←
    usedTheorems.map.foldlM (init := ({}, 0)) λ (map, size) origin thm => do
      if isGlobalSimpTheorem simpTheorems simprocs origin then
        return (map, size)
      else
        return (map.insert origin thm, size + 1)
  let stx ←
    match ← simpAllOrSimpAtStarOnlyStx simpAll inGoal configStx? { map, size } with
    | `(tactic| simp_all $[$cfg:config]? only [$lems,*]) =>
      `(tactic| simp_all $[$cfg]? [$lems,*])
    | `(tactic| simp $[$cfg:config]? only [$lems,*] at *) =>
      `(tactic| simp $[$cfg]? [$lems,*] at *)
    | `(tactic| simp_all $[$cfg:config]? only) =>
      `(tactic| simp_all $[$cfg]?)
    | `(tactic| simp $[$cfg:config]? only at *) =>
      `(tactic| simp $[$cfg]? at *)
    | stx => throwError "simp tactic builder: unexpected syntax:{indentD stx}"
  return .unstructured ⟨stx⟩

def intros (postGoal : MVarId) (newFVarIds : Array FVarId)
    (md : TransparencyMode) : TacticBuilder := do
  let newFVarUserNames ← postGoal.withContext $
    newFVarIds.mapM (mkIdent <$> ·.getUserName)
  let tac ← `(tactic| intro $newFVarUserNames:ident*)
  let tac := withAllTransparencySyntax md tac
  return .unstructured ⟨tac⟩

def splitTarget : TacticBuilder :=
  return .unstructured $ ← `(tactic| split)

def splitAt (goal : MVarId) (fvarId : FVarId) : TacticBuilder := do
  let name ← goal.withContext fvarId.getUserName
  let tac ← `(tactic| split at $(mkIdent name):ident)
  return .unstructured tac

def substFVars (goal : MVarId) (fvarIds : Array FVarId) : TacticBuilder := do
  let names ← goal.withContext $ fvarIds.mapM λ fvarId =>
    return mkIdent (← fvarId.getUserName)
  let tac ← `(tactic| subst $names:ident*)
  return .unstructured tac

def substFVars' (fvarUserNames : Array Name) : TacticBuilder := do
  let fvarUserNames := fvarUserNames.map mkIdent
  let tac ← `(tactic| subst $fvarUserNames:ident*)
  return .unstructured tac

end Script.TacticBuilder

open Script

def assertHypothesisS (goal : MVarId) (h : Hypothesis) (md : TransparencyMode) :
    ScriptM (MVarId × Array FVarId) :=
  withScriptStep goal (#[·.1]) (λ _ => true) tacticBuilder do
    let (fvarIds, goal) ← withTransparency md $ goal.assertHypotheses #[h]
    return (goal, fvarIds)
where
  tacticBuilder _ := TacticBuilder.assertHypothesis goal h md

def applyS (goal : MVarId) (e : Expr) (eStx? : Option Term)
    (md : TransparencyMode) : ScriptM (Array MVarId) :=
  withScriptStep goal id (λ _ => true) tacticBuilder do
    (·.toArray) <$> withTransparency md (goal.apply e)
where
  tacticBuilder _ :=
      match eStx? with
      | none => TacticBuilder.apply goal e md
      | some eStx => TacticBuilder.applyStx eStx md

def replaceFVarS (goal : MVarId) (fvarId : FVarId) (type : Expr) (proof : Expr) :
    ScriptM (MVarId × FVarId × Bool) :=
  withScriptStep goal (#[·.1]) (λ _ => true) tacticBuilder do
    replaceFVar goal fvarId type proof
where
  tacticBuilder := (TacticBuilder.replace goal ·.1 fvarId type proof)

def clearS (goal : MVarId) (fvarId : FVarId) : ScriptM MVarId :=
  withScriptStep goal (#[·]) (λ _ => true) tacticBuilder do
    goal.clear fvarId
where
  tacticBuilder _ := TacticBuilder.clear goal #[fvarId]

def tryClearS (goal : MVarId) (fvarId : FVarId) : ScriptM (Option MVarId) :=
  withOptScriptStep goal (#[·]) tacticBuilder do
    goal.tryClear fvarId
where
  tacticBuilder _ := TacticBuilder.clear goal #[fvarId]

def tryClearManyS (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptM (MVarId × Array FVarId) :=
  withScriptStep goal (#[·.fst]) (! ·.2.isEmpty) tacticBuilder do
    goal.tryClearMany' fvarIds
where
  tacticBuilder := λ (_, fvarIds) => TacticBuilder.clear goal fvarIds

def tryCasesS (goal : MVarId) (fvarId : FVarId) (ctorNames : Array CtorNames) :
    ScriptM (Option (Array CasesSubgoal)) := do
  let ctorNames := getUnusedCtorNames (← goal.getDecl).lctx
  let tacticBuilder _ :=
    TacticBuilder.casesOrObtain goal (.fvar fvarId) ctorNames
  withOptScriptStep goal (·.map (·.mvarId)) tacticBuilder do
    observing? $ goal.cases fvarId (ctorNames.map (·.toAltVarNames))
      (useNatCasesAuxOn := true)
where
  getUnusedCtorNames (lctx : LocalContext) : Array CtorNames :=
    Prod.fst $ ctorNames.foldl (init := (Array.mkEmpty ctorNames.size, lctx))
      λ (ctorNames, lctx) cn =>
        let (cn, lctx) := cn.mkFreshArgNames lctx
        (ctorNames.push cn, lctx)

def renameInaccessibleFVarsS (goal : MVarId) :
    ScriptM (MVarId × Array FVarId) :=
  withScriptStep goal (#[·.1]) (! ·.snd.isEmpty) tacticBuilder do
    goal.renameInaccessibleFVars
where
  tacticBuilder := λ (goal, renamedFVars) =>
    TacticBuilder.renameInaccessibleFVars goal renamedFVars

def unfoldManyTargetS (unfold? : Name → Option (Option Name)) (goal : MVarId) :
    ScriptM (Option (MVarId × Array Name)) := do
  let preState ← show MetaM _ from saveState
  let some (postGoal, usedDecls) ← unfoldManyTarget unfold? goal
    | return none
  let postState ← show MetaM _ from saveState
  recordScriptStep {
    preGoal := goal
    tacticBuilders :=
      #[TacticBuilder.unfold usedDecls (aesopUnfold := false),
        TacticBuilder.unfold usedDecls (aesopUnfold := true)]
    postGoals := #[postGoal]
    preState, postState
  }
  return some (postGoal, usedDecls)

def unfoldManyAtS (unfold? : Name → Option (Option Name)) (goal : MVarId)
    (fvarId : FVarId) : ScriptM (Option (MVarId × Array Name)) := do
  let preState ← show MetaM _ from saveState
  let some (postGoal, usedDecls) ← unfoldManyAt unfold? goal fvarId
    | return none
  let postState ← show MetaM _ from saveState
  recordScriptStep {
    preGoal := goal
    tacticBuilders :=
      #[TacticBuilder.unfoldAt goal fvarId usedDecls (aesopUnfold := false),
        TacticBuilder.unfoldAt goal fvarId usedDecls (aesopUnfold := true)]
    postGoals := #[postGoal]
    preState, postState
  }
  return some (postGoal, usedDecls)

def unfoldManyStarS (goal : MVarId) (unfold? : Name → Option (Option Name))  :
    ScriptM (Option MVarId) :=
  goal.withContext do
    let initialGoal := goal
    let mut goal := goal
    if let some (goal', _) ← unfoldManyTargetS unfold? goal then
      goal := goal'
    for ldecl in (← goal.getDecl).lctx do
      if ldecl.isImplementationDetail then
        continue
      if let some (goal', _) ← unfoldManyAtS unfold? goal ldecl.fvarId then
        goal := goal'
    if goal == initialGoal then
      return none
    else
      return some goal

def introsS (goal : MVarId) : ScriptM (MVarId × Array FVarId) :=
  withScriptStep goal (#[·.fst]) (! ·.2.isEmpty) tacticBuilder do
    let (newFVarIds, mvarId) ← unhygienic $ goal.intros
    return (mvarId, newFVarIds)
where
  tacticBuilder := λ (postGoal, newFVarIds) =>
      TacticBuilder.intros postGoal newFVarIds .default

def introsUnfoldingS (goal : MVarId) (md : TransparencyMode) :
    ScriptM (MVarId × Array FVarId) :=
  withScriptStep goal (#[·.fst]) (! ·.2.isEmpty) tacticBuilder do
    let (newFVarIds, mvarId) ← withTransparency md $ unhygienic $
      introsUnfolding goal
    return (mvarId, newFVarIds)
where
  tacticBuilder := λ (postGoal, newFVarIds) =>
      TacticBuilder.intros postGoal newFVarIds md

def straightLineExtS (goal : MVarId) : ScriptM ExtResult :=
  withScriptStep goal (·.goals.map (·.1)) (·.depth != 0) tacticBuilder do
    unhygienic $ straightLineExt goal
where
  tacticBuilder := TacticBuilder.extN

def tryExactFVarS (goal : MVarId) (fvarId : FVarId) (md : TransparencyMode) :
    ScriptM Bool := do
  let preState ← show MetaM _ from saveState
  let ldecl ← fvarId.getDecl
  let tgt ← goal.getType
  if ! (← withTransparency md $ isDefEq ldecl.type tgt) then
    show MetaM _ from restoreState preState
    return false
  goal.assign ldecl.toExpr
  let postState ← show MetaM _ from saveState
  let step := {
    preGoal := goal
    postGoals := #[]
    tacticBuilders := #[TacticBuilder.exactFVar goal fvarId md]
    preState, postState
  }
  recordScriptStep step
  return true

private def renameInaccessibleFVarsS' (goals : Array MVarId) :
    ScriptM (Array MVarId) :=
  goals.mapM ((·.fst) <$> renameInaccessibleFVarsS ·)

def splitTargetS? (goal : MVarId) :
    ScriptM (Option (Array MVarId)) := do
  let some subgoals ← withOptScriptStep goal id tacticBuilder do
    (·.map (·.toArray)) <$> splitTarget? goal
    | return none
  some <$> renameInaccessibleFVarsS' subgoals
where
  tacticBuilder _ := TacticBuilder.splitTarget

def splitFirstHypothesisS? (goal : MVarId) :
    ScriptM (Option (Array MVarId)) := do
  let some (subgoals, _) ← withOptScriptStep goal (·.1) tacticBuilder do
    for ldecl in (← goal.getDecl).lctx do
      if ldecl.isImplementationDetail then
        continue
      if let some goals ← splitLocalDecl? goal ldecl.fvarId then
        return some (goals.toArray, ldecl.fvarId)
    return none
    | return none
  some <$> renameInaccessibleFVarsS' subgoals
where
  tacticBuilder := λ (_, fvarId) => TacticBuilder.splitAt goal fvarId

end Aesop
