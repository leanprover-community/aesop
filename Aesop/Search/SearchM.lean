/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Search.Queue
import Aesop.RuleSet

open Lean

namespace Aesop.SearchM

structure Context where
  ruleSet : RuleSet
  options : Aesop.Options
  rootGoalMVar : MVarId -- TODO this is now the root goal's `preNormGoal`
  deriving Inhabited

structure State (Q) [Aesop.Queue Q] where
  iteration : Iteration
  queue : Q
  deriving Inhabited

end SearchM

abbrev SearchM Q [Aesop.Queue Q] :=
  ReaderT SearchM.Context $ StateRefT (SearchM.State Q) $ StateRefT Tree MetaM

variable [Aesop.Queue Q]

namespace SearchM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance [Monad m] : Monad (SearchM Q) :=
  { inferInstanceAs (Monad (SearchM Q)) with }

instance : Inhabited (SearchM Q α) where
  default := failure

instance : MonadLift TreeM (SearchM Q) where
  monadLift x := do
    let ctx := { currentIteration := (← get).iteration }
    liftM $ ReaderT.run x ctx

def run' (ctx : SearchM.Context) (σ : SearchM.State Q) (t : Tree)
    (x : SearchM Q α) : MetaM (α × SearchM.State Q × Tree) := do
  let ((a, σ), t) ← ReaderT.run x ctx |>.run σ |>.run t
  return (a, σ, t)

def run (ruleSet : RuleSet) (options : Aesop.Options) (goal : MVarId)
    (x : SearchM Q α) : MetaM α := do
  let t ← mkInitialTree goal
  let ctx := { ruleSet, options, rootGoalMVar := goal }
  let #[rootGoal] := (← t.root.get).goals
    | throwError "aesop: internal error: root mvar cluster does not contain exactly one goal."
  let state := { queue := ← Queue.init' #[rootGoal], iteration := Iteration.one }
  let ((a, _), _) ← ReaderT.run x ctx |>.run state |>.run t
  return a

end SearchM

def getSearchState : SearchM Q (SearchM.State Q) :=
  getThe (SearchM.State _)

def setSearchState : SearchM.State Q → SearchM Q Unit :=
  setThe (SearchM.State _)

def modifySearchState : (SearchM.State Q → SearchM.State Q) → SearchM Q Unit :=
  modifyThe (SearchM.State Q)

def getTree : SearchM Q Tree :=
  getThe Tree

def setTree : Tree → SearchM Q Unit :=
  setThe Tree

def modifyTree : (Tree → Tree) → SearchM Q Unit :=
  modifyThe Tree

def getIteration : SearchM Q Iteration :=
  return (← getSearchState).iteration

def incrementIteration : SearchM Q Unit :=
  modifySearchState λ s => { s with iteration := s.iteration.succ }

def popGoal? : SearchM Q (Option GoalRef) := do
  let s ← getSearchState
  let (goal?, queue) ← Queue.popGoal s.queue
  setSearchState { s with queue }
  return goal?

def enqueueGoals (gs : Array GoalRef) : SearchM Q Unit := do
  let s ← getSearchState
  let queue ← Queue.addGoals s.queue gs
  setSearchState { s with queue }

def formatQueue : SearchM Q MessageData := do
  Queue.format (← getSearchState).queue

end Aesop
