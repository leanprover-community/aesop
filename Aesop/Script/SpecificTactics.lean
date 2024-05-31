/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.CtorNames
import Aesop.Script.ScriptBuilder
import Batteries.Lean.Meta.Clear
import Batteries.Lean.Meta.Inaccessible

open Lean
open Lean.Meta
open Lean.PrettyPrinter (delab)

namespace Aesop.ScriptBuilder

def replace (preGoal postGoal : MVarId) (userName : Name) (type : Expr) (proof : Expr) :
    ScriptBuilder MetaM :=
  .ofTactics 1 $ do
    let type ← postGoal.withContext $ delab type
    let proof ← preGoal.withContext $ delab proof
    return #[← `(tactic| replace $(mkIdent userName) : $type := $proof)]

def assertHypotheses (goal : MVarId) (hs : Array Hypothesis) :
    ScriptBuilder MetaM :=
  .ofTactics 1 $ goal.withContext $ hs.mapM λ h => do
    `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))

def clear (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptBuilder MetaM :=
  .ofTactic 1 $ goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    `(tactic| clear $userNames*)

def rcases (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    ScriptBuilder MetaM :=
  .ofTactic ctorNames.size $ goal.withContext do
    let pat ← ctorNamesToRCasesPats ctorNames
    `(tactic| rcases $(← delab e):term with $pat)

def obtain (goal : MVarId) (e : Expr) (ctorNames : CtorNames) :
    ScriptBuilder MetaM :=
  .ofTactic 1 $ goal.withContext do
    `(tactic| obtain $(← ctorNames.toRCasesPat) := $(← delab e))

def rcasesOrObtain (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    ScriptBuilder MetaM :=
  if h : ctorNames.size = 1 then
    obtain goal e ctorNames[0]
  else
    rcases goal e ctorNames

def renameInaccessibleFVars (goal : MVarId) (renamedFVars : Array FVarId) :
    ScriptBuilder MetaM :=
  if renamedFVars.isEmpty then
    .id
  else
    .ofTactic 1 $ goal.withContext do
      let ids ← renamedFVars.mapM λ fvarId => do
        let userName := mkIdent (← fvarId.getDecl).userName
        `(binderIdent| $userName:ident)
      `(tactic| rename_i $ids:binderIdent*)

def unfoldManyStar (usedDecls : HashSet Name) : ScriptBuilder MetaM :=
  if usedDecls.isEmpty then
    .id
  else
    .ofTactic 1 `(tactic| aesop_unfold [$(usedDecls.toArray.map mkIdent):ident,*])

def unhygienicExt (subgoals : Nat) : ScriptBuilder MetaM :=
  .ofTactic subgoals `(tactic| unhygienic ext)

end ScriptBuilder

def assertHypothesesWithScript (goal : MVarId)
    (hs : Array Hypothesis) (generateScript : Bool) :
    MetaM (Array FVarId × MVarId × Option (ScriptBuilder MetaM)) := do
  let (fvarIds, goal') ← goal.assertHypotheses hs
  let scriptBuilder? := mkScriptBuilder? generateScript $ .assertHypotheses goal hs
  return (fvarIds, goal', scriptBuilder?)

def replaceFVarWithScript (goal : MVarId) (fvarId : FVarId) (type : Expr)
    (proof : Expr) (generateScript : Bool) :
    MetaM (MVarId × FVarId × Option (ScriptBuilder MetaM)) := do
  let userName ← fvarId.getUserName
  let (postGoal, newFVarId, _) ← replaceFVar goal fvarId type proof
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .replace goal postGoal userName type proof
  return (postGoal, newFVarId, scriptBuilder?)

def clearWithScript (goal : MVarId) (fvarId : FVarId) (generateScript : Bool) :
    MetaM (MVarId × Option (ScriptBuilder MetaM)) :=
  let scriptBuilder? := mkScriptBuilder? generateScript $ .clear goal #[fvarId]
  return (← goal.clear fvarId, scriptBuilder?)

def tryClearWithScript (goal : MVarId) (fvarId : FVarId) (generateScript : Bool) :
    MetaM (MVarId × Option (ScriptBuilder MetaM)) := do
  let goal' ← goal.tryClear fvarId
  let scriptBuilder? := mkScriptBuilder? generateScript $
    if goal' == goal then
      .id
    else
      .clear goal #[fvarId]
  return (goal', scriptBuilder?)

def tryClearManyWithScript (goal : MVarId) (fvarIds : Array FVarId)
    (generateScript : Bool) :
    MetaM (MVarId × Array FVarId × Option (ScriptBuilder MetaM)) := do
  let (goal', cleared) ← goal.tryClearMany' fvarIds
  let scriptBuilder? := mkScriptBuilder? generateScript $ .clear goal cleared
  return (goal', cleared, scriptBuilder?)

def casesWithScript (goal : MVarId) (fvarId : FVarId)
    (ctorNames : Array CtorNames) (generateScript : Bool) :
    MetaM (Array CasesSubgoal × Option (ScriptBuilder MetaM)) := do
  let ctorNames := getUnusedCtorNames (← goal.getDecl).lctx
  let goals ← goal.cases fvarId (ctorNames.map (·.toAltVarNames))
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .rcasesOrObtain goal (.fvar fvarId) ctorNames
  return (goals, scriptBuilder?)
where
  getUnusedCtorNames (lctx : LocalContext) : Array CtorNames :=
    Prod.fst $ ctorNames.foldl (init := (Array.mkEmpty ctorNames.size, lctx))
      λ (ctorNames, lctx) cn =>
        let (cn, lctx) := cn.mkFreshArgNames lctx
        (ctorNames.push cn, lctx)

def renameInaccessibleFVarsWithScript (goal : MVarId) (generateScript : Bool) :
    MetaM (MVarId × Array FVarId × Option (ScriptBuilder MetaM)) := do
  let (goal, renamedFVars) ← goal.renameInaccessibleFVars
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .renameInaccessibleFVars goal renamedFVars
  return (goal, renamedFVars, scriptBuilder?)

def unfoldManyStarWithScript (goal : MVarId)
    (unfold? : Name → Option (Option Name)) (generateScript : Bool) :
    MetaM (UnfoldResult MVarId × Option (ScriptBuilder MetaM)) := do
  let result ← unfoldManyStar goal unfold?
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .unfoldManyStar result.usedDecls
  return (result, scriptBuilder?)

end Aesop
