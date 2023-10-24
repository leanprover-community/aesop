/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Search.Expansion.Simp
import Aesop.Search.Queue.Class
import Aesop.Profiling
import Aesop.RuleSet

open Lean
open Lean.Meta

namespace Aesop

structure NormSimpContext extends Simp.Context where
  enabled : Bool
  useHyps : Bool
  configStx? : Option Term
  deriving Inhabited

namespace SearchM

structure Context where
  ruleSet : RuleSet
  normSimpContext : NormSimpContext
  options : Aesop.Options'
  profilingEnabled : Bool
  deriving Nonempty

def Context.normSimpConfig (ctx : Context) : SimpConfig where
  useHyps := ctx.normSimpContext.useHyps
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

instance : MonadRef (SearchM Q) :=
  { inferInstanceAs (MonadRef (SearchM Q)) with }

instance : Inhabited (SearchM Q α) where
  default := failure

instance : MonadLift TreeM (SearchM Q) where
  monadLift x := do
    let ctx := { currentIteration := (← get).iteration }
    liftM $ ReaderT.run x ctx

instance : MonadState (State Q) (SearchM Q) :=
  { inferInstanceAs (MonadStateOf (State Q) (SearchM Q)) with }

instance : MonadReader Context (SearchM Q) :=
  { inferInstanceAs (MonadReaderOf Context (SearchM Q)) with }

instance : MonadReaderOf ProfileT.Context (SearchM Q) where
  read := return ⟨(← read).profilingEnabled⟩

instance : MonadStateOf Profile (SearchM Q) where
  get := return (← getThe (State Q)).profile
  set profile := modify λ s => { s with profile }
  modifyGet f := modifyGet λ s =>
    let (result, profile) := f s.profile
    (result, { s with profile })

instance [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLift m (SearchM Q)] :
    MonadLift (ProfileT m) (SearchM Q) where
  monadLift x := do
    let profile ← modifyGetThe Profile λ profile => (profile, {})
    let (result, profile) ← x.run (← read).profilingEnabled profile
    setThe Profile profile
    return result

def run' (ctx : SearchM.Context) (σ : SearchM.State Q) (t : Tree)
    (x : SearchM Q α) : MetaM (α × SearchM.State Q × Tree) := do
  let ((a, σ), t) ← ReaderT.run x ctx |>.run σ |>.run t
  return (a, σ, t)

def run (ruleSet : RuleSet) (options : Aesop.Options')
    (simpConfig : Aesop.SimpConfig) (simpConfigStx? : Option Term)
    (goal : MVarId) (profile : Profile) (x : SearchM Q α) :
    MetaM (α × State Q × Tree) := do
  let t ← mkInitialTree goal
  let profilingEnabled := (← getOptions).getBool `profiler
  let normSimpContext := {
    (← Simp.Context.mkDefault) with
    config := simpConfig.toConfig
    simpTheorems := ruleSet.globalNormSimpTheorems
    configStx? := simpConfigStx?
    enabled := simpConfig.enabled
    useHyps := simpConfig.useHyps
  }
  let ctx := { ruleSet, options, profilingEnabled, normSimpContext }
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

def setMaxRuleApplicationDepthReached : SearchM Q Unit :=
  modify λ s => { s with maxRuleApplicationDepthReached := true }

def wasMaxRuleApplicationDepthReached : SearchM Q Bool :=
  return (← get).maxRuleApplicationDepthReached

end Aesop
