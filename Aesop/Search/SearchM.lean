/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Search.Expansion.Simp
import Aesop.Search.Queue.Class
import Aesop.Stats.Basic
import Aesop.RuleSet

open Lean
open Lean.Meta

namespace Aesop

structure NormSimpContext extends Simp.Context where
  enabled : Bool
  useHyps : Bool
  configStx? : Option Term
  simprocs : Simp.SimprocsArray
  deriving Inhabited

namespace SearchM

structure Context where
  ruleSet : LocalRuleSet
  normSimpContext : NormSimpContext
  options : Aesop.Options'
  statsRef : StatsRef
  deriving Nonempty

structure State (Q) [Aesop.Queue Q] where
  iteration : Iteration
  queue : Q
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

instance : MonadState (State Q) (SearchM Q) :=
  { inferInstanceAs (MonadStateOf (State Q) (SearchM Q)) with }

instance : MonadReader Context (SearchM Q) :=
  { inferInstanceAs (MonadReaderOf Context (SearchM Q)) with }

instance : MonadStats (SearchM Q) where
  readStatsRef := return (← read).statsRef

instance : MonadLift TreeM (SearchM Q) where
  monadLift x := do
    let ctx := { currentIteration := (← get).iteration }
    liftM $ ReaderT.run x ctx

protected def run' (ctx : SearchM.Context) (σ : SearchM.State Q) (t : Tree)
    (x : SearchM Q α) : MetaM (α × SearchM.State Q × Tree × Stats) := do
  let ((a, σ), t) ←
    x.run ctx |>.run σ |>.run t
  return (a, σ, t, ← ctx.statsRef.get)

protected def run (ruleSet : LocalRuleSet) (options : Aesop.Options')
    (simpConfig : Simp.Config) (simpConfigStx? : Option Term)
    (goal : MVarId) (stats : Stats) (x : SearchM Q α) :
    MetaM (α × State Q × Tree × Stats) := do
  let t ← mkInitialTree goal
  let normSimpContext := {
    config := simpConfig
    maxDischargeDepth := UInt32.ofNatTruncate simpConfig.maxDischargeDepth
    simpTheorems := ruleSet.simpTheoremsArray.map (·.snd)
    congrTheorems := ← getSimpCongrTheorems
    simprocs := ruleSet.simprocsArray.map (·.snd)
    configStx? := simpConfigStx?
    enabled := options.enableSimp
    useHyps := options.useSimpAll
  }
  let statsRef ← IO.mkRef stats
  let ctx := { ruleSet, options, normSimpContext, statsRef }
  let #[rootGoal] := (← t.root.get).goals
    | throwError "aesop: internal error: root mvar cluster does not contain exactly one goal."
  let state := {
    queue := ← Queue.init' #[rootGoal]
    iteration := Iteration.one
    maxRuleApplicationDepthReached := false
  }
  x.run' ctx state t

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
