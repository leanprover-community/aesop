/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.BaseM
import Aesop.Script.Step
import Aesop.Script.Tactic

open Lean Aesop.Script

namespace Aesop

abbrev ScriptT m := StateRefT' IO.RealWorld (Array LazyStep) m

namespace ScriptT

protected def run [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : ScriptT m α) :
    m (α × Array LazyStep) :=
  StateRefT'.run x #[]

end ScriptT

abbrev ScriptM := ScriptT BaseM

variable [MonadStateOf (Array LazyStep) m]

def recordScriptStep (step : LazyStep) : m Unit :=
  modify (·.push step)

def recordScriptSteps (steps : Array LazyStep) : m Unit :=
  modify (· ++ steps)

def withScriptStep (preGoal : MVarId) (postGoals : α → Array MVarId)
    (success : α → Bool) (tacticBuilder : α → TacticBuilder) (x : MetaM α) :
    ScriptM α := do
  let preState ← show MetaM _ from saveState
  let a ← x
  if success a then
    let postState ← show MetaM _ from saveState
    recordScriptStep {
      tacticBuilders := #[tacticBuilder a]
      postGoals := postGoals a
      preGoal, preState, postState
    }
  return a

def withOptScriptStep (preGoal : MVarId) (postGoals : α → Array MVarId)
    (tacticBuilder : α → TacticBuilder) (x : MetaM (Option α)) :
    ScriptM (Option α) := do
  let preState ← show MetaM _ from saveState
  let some a ← x
    | return none
  let postState ← show MetaM _ from saveState
  recordScriptStep {
    tacticBuilders := #[tacticBuilder a]
    postGoals := postGoals a
    preGoal, preState, postState
  }
  return some a

end Aesop
