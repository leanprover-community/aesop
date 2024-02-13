/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.ScriptBuilder
import Batteries.Lean.Meta.Clear
import Batteries.Lean.Meta.Inaccessible

open Lean
open Lean.Meta
open Lean.PrettyPrinter (delab)

namespace Aesop.ScriptBuilder

def assertHypotheses (goal : MVarId) (hs : Array Hypothesis) :
    ScriptBuilder MetaM :=
  .ofTactics 1 $ goal.withContext $ hs.mapM λ h => do
    `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))

def clear (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptBuilder MetaM :=
  .ofTactic 1 $ goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    `(tactic| clear $userNames*)

def unhygienicAesopCases (goal : MVarId) (fvarId : FVarId) (subgoals : Nat) :
    ScriptBuilder MetaM :=
  .ofTactic subgoals do
    let userName ← goal.withContext fvarId.getUserName
    `(tactic| unhygienic aesop_cases $(mkIdent userName):ident)

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

def unhygienicCasesWithScript (goal : MVarId) (fvarId : FVarId)
    (generateScript : Bool) :
    MetaM (Array CasesSubgoal × Option (ScriptBuilder MetaM)) := do
  let goals ← unhygienic $ goal.cases fvarId
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .unhygienicAesopCases goal fvarId goals.size
  return (goals, scriptBuilder?)

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
