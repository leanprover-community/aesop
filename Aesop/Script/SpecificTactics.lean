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
import Batteries.Lean.Meta.Clear
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

def rcases (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder := do
  goal.withContext do
    let pat := ctorNamesToRCasesPats ctorNames
    return .unstructured $ ← `(tactic| rcases $(← delab e):term with $pat)

def obtain (goal : MVarId) (e : Expr) (ctorNames : CtorNames) : TacticBuilder :=
  goal.withContext do
    let tac ← `(tactic| obtain $(ctorNames.toRCasesPat) := $(← delab e))
    return .unstructured tac

def rcasesOrObtain (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder :=
  if h : ctorNames.size = 1 then
    obtain goal e ctorNames[0]
  else
    rcases goal e ctorNames

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

def aesopUnfold (usedDecls : HashSet Name) : TacticBuilder := do
  if usedDecls.isEmpty then
    return .skip
  else do
    let tac ← `(tactic| aesop_unfold [$(usedDecls.toArray.map mkIdent):ident,*])
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
  let tac ←
    if r.depth == 1 then
      `(tactic| ext1 $pats:rintroPat*)
    else
      let depth := Syntax.mkNumLit $ toString r.depth
      `(tactic| ext $pats:rintroPat* : $depth)
  return .unstructured tac
where
  mkPat (fvarId : FVarId) : MetaM (TSyntax `rintroPat) := do
    `(rintroPat| $(mkIdent $ ← fvarId.getUserName):ident)

def simpAllOrSimpAtStarOnly (simpAll : Bool) (inGoal : MVarId)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    TacticBuilder := do
  let originalStx ←
    if simpAll then
      match configStx? with
      | none => `(tactic| simp_all)
      | some cfg => `(tactic| simp_all (config := $cfg))
    else
      match configStx? with
      | none => `(tactic| simp at *)
      | some cfg => `(tactic| simp (config := $cfg) at *)
  let stx ← inGoal.withContext do
    Elab.Tactic.mkSimpOnly originalStx usedTheorems
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
    ScriptM (MVarId × FVarId) :=
  withScriptStep goal (#[·.1]) (λ _ => true) tacticBuilder do
    let (postGoal, newFVarId, _) ← replaceFVar goal fvarId type proof
    return (postGoal, newFVarId)
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
    TacticBuilder.rcasesOrObtain goal (.fvar fvarId) ctorNames
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

def unfoldManyStarS (goal : MVarId) (unfold? : Name → Option (Option Name))  :
    ScriptM (UnfoldResult MVarId) := do
  let preState ← show MetaM _ from saveState
  let .changed postGoal usedDecls ← unfoldManyStar goal unfold?
    | return .unchanged
  let postState ← show MetaM _ from saveState
  let step := {
    preGoal := goal
    tacticBuilder := TacticBuilder.aesopUnfold usedDecls
    postGoals := #[postGoal]
    preState, postState
  }
  recordScriptStep step
  return .changed postGoal usedDecls

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
    tacticBuilder := TacticBuilder.exactFVar goal fvarId md
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
