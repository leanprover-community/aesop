/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Search.Expansion.Simp.Basic
import Aesop.Search.Queue.Class
import Aesop.Profiling
import Aesop.RuleSet

open Lean
open Lean.Meta

namespace Aesop.SearchM

structure Context where
  ruleSet : RuleSet
  normSimpContext : Simp.Context
  normSimpConfigSyntax? : Option Term
  normSimpUseHyps : Bool
  options : Aesop.Options
  profilingEnabled : Bool
  originalMetaState : Meta.SavedState
    -- The MetaM state before preprocessing.
  originalGoal : MVarId
    -- The goal before preprocessing.
  preprocessingScript : UnstructuredScript
    -- The script for tactics executed during preprocessing.
  deriving Inhabited

def Context.normSimpConfig (ctx : Context) : SimpConfig where
  useHyps := ctx.normSimpUseHyps
  toConfigCtx := { ctx.normSimpContext.config with }

structure State (Q) [Aesop.Queue Q] where
  iteration : Iteration
  queue : Q
  profile : Profile
  maxRuleApplicationDepthReached : Bool
  deriving Inhabited

end SearchM

abbrev SearchM Q [Aesop.Queue Q] :=
  ReaderT SearchM.Context $ StateRefT (SearchM.State Q) $ StateRefT Tree MetaM

variable [Aesop.Queue Q]

namespace SearchM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad (SearchM Q) :=
  { inferInstanceAs (Monad (SearchM Q)) with }

instance : Inhabited (SearchM Q α) where
  default := failure

instance : MonadLift TreeM (SearchM Q) where
  monadLift x := do
    let ctx := { currentIteration := (← get).iteration }
    liftM $ ReaderT.run x ctx

instance (priority := high) : MonadState (State Q) (SearchM Q) :=
  { inferInstanceAs (MonadStateOf (State Q) (SearchM Q)) with }

instance (priority := high) : MonadReader Context (SearchM Q) :=
  { inferInstanceAs (MonadReaderOf Context (SearchM Q)) with }

instance : MonadReaderOf ProfileT.Context (SearchM Q) where
  read := return ⟨(← read).profilingEnabled⟩

instance : MonadStateOf Profile (SearchM Q) where
  get := return (← getThe (State Q)).profile
  set profile := modify λ s => { s with profile }
  modifyGet f := modifyGet λ s =>
    let (result, profile) := f s.profile
    (result, { s with profile })

def run' (ctx : SearchM.Context) (σ : SearchM.State Q) (t : Tree)
    (x : SearchM Q α) : MetaM (α × SearchM.State Q × Tree) := do
  let ((a, σ), t) ← ReaderT.run x ctx |>.run σ |>.run t
  return (a, σ, t)

def run (ruleSet : RuleSet) (options : Aesop.Options)
    (simpConfig : Aesop.SimpConfig) (simpConfigSyntax? : Option Term)
    (goal : MVarId) (originalMetaState : Meta.SavedState)
    (originalGoal : MVarId) (preprocessingScript : UnstructuredScript)
    (profile : Profile) (x : SearchM Q α) : MetaM (α × State Q × Tree) := do
  let t ← mkInitialTree goal
  let profilingEnabled ← TraceOption.profile.isEnabled
  let normSimpContext := {
    (← Simp.Context.mkDefault) with
    simpTheorems := #[ruleSet.normSimpLemmas]
    config := simpConfig.toConfig
  }
  let ctx := {
    normSimpUseHyps := simpConfig.useHyps
    normSimpConfigSyntax? := simpConfigSyntax?
    ruleSet, options, profilingEnabled, normSimpContext, originalMetaState,
    originalGoal, preprocessingScript
  }
  let #[rootGoal] := (← t.root.get).goals
    | throwError "aesop: internal error: root mvar cluster does not contain exactly one goal."
  let state := {
    queue := ← Queue.init' #[rootGoal]
    iteration := Iteration.one
    profile
    maxRuleApplicationDepthReached := false
  }
  let ((a, state), tree) ← ReaderT.run x ctx |>.run state |>.run t
  return (a, state, tree)

end SearchM

def getTree : SearchM Q Tree :=
  getThe Tree

def setTree : Tree → SearchM Q Unit :=
  setThe Tree

def modifyTree : (Tree → Tree) → SearchM Q Unit :=
  modifyThe Tree

def getIteration : SearchM Q Iteration :=
  return (← get).iteration

def incrementIteration : SearchM Q Unit :=
  modify λ s => { s with iteration := s.iteration.succ }

def popGoal? : SearchM Q (Option GoalRef) := do
  let s ← get
  let (goal?, queue) ← Queue.popGoal s.queue
  set { s with queue }
  return goal?

def enqueueGoals (gs : Array GoalRef) : SearchM Q Unit := do
  let s ← get
  let queue ← Queue.addGoals s.queue gs
  set { s with queue }

def formatQueue : SearchM Q MessageData := do
  Queue.format (← get).queue

def setMaxRuleApplicationDepthReached : SearchM Q Unit :=
  modify λ s => { s with maxRuleApplicationDepthReached := true }

def wasMaxRuleApplicationDepthReached : SearchM Q Bool :=
  return (← get).maxRuleApplicationDepthReached

end Aesop
