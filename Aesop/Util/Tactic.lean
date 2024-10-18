/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean
import Batteries.Tactic.OpenPrivate

open Lean Lean.Meta Lean.Elab.Tactic

namespace Aesop

/--
A `MetaM` version of the `replace` tactic. If `fvarId` refers to the
hypothesis `h`, this tactic asserts a new hypothesis `h : type` with proof
`proof : type` and then tries to clear `fvarId`. Unlike `replaceLocalDecl`,
`replaceFVar` always adds the new hypothesis at the end of the local context.

`replaceFVar` returns the new goal, the `FVarId` of the newly asserted
hypothesis and whether the old hypothesis was cleared.
-/
def replaceFVar (goal : MVarId) (fvarId : FVarId) (type : Expr) (proof : Expr) :
    MetaM (MVarId × FVarId × Bool) := do
  let userName ← goal.withContext $ fvarId.getUserName
  let preClearGoal ← goal.assert userName type proof
  let goal ← preClearGoal.tryClear fvarId
  let clearSuccess := preClearGoal != goal
  let (newFVarId, goal) ← intro1Core goal (preserveBinderNames := true)
  return (goal, newFVarId, clearSuccess)

/-- Introduce as many binders as possible while unfolding definitions with the
ambient transparency. -/
partial def introsUnfolding (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  run mvarId #[]
where
  run (mvarId : MVarId) (fvars : Array FVarId) : MetaM (Array FVarId × MVarId) :=
    mvarId.withContext do
      let type ← whnf (← mvarId.getType)
      let size := getIntrosSize type
      if 0 < size then
        let (fvars', mvarId') ← mvarId.introN size
        run mvarId' (fvars ++ fvars')
      else
        return (fvars, mvarId)

end Aesop
