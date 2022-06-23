/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Constants
import Aesop.Tree.BranchState
import Aesop.Tree.UnsafeQueue
import Std

open Lean
open Lean.Meta
open Std

private def Bool.toYesNo : Bool → Format
  | true => "yes"
  | false => "no "

namespace Aesop

/-! ## Node IDs -/

-- TODO Change to USize?
structure GoalId where
  toNat : Nat
  deriving Inhabited, DecidableEq

namespace GoalId

protected def zero : GoalId :=
  ⟨0⟩

protected def one : GoalId :=
  ⟨1⟩

protected def succ : GoalId → GoalId
  | ⟨n⟩ => ⟨n + 1⟩

def dummy : GoalId :=
  ⟨1000000000000000⟩

instance : LT GoalId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := GoalId) (· < ·) :=
  λ n m => inferInstanceAs (Decidable (n.toNat < m.toNat))

instance : ToString GoalId where
  toString n := toString n.toNat

instance : Hashable GoalId where
  hash n := hash n.toNat

end GoalId


/-! ## Rule Application IDs -/

structure RappId where
  toNat : Nat
  deriving Inhabited, DecidableEq

namespace RappId

protected def zero : RappId :=
  ⟨0⟩

protected def succ : RappId → RappId
  | ⟨n⟩ => ⟨n + 1⟩

protected def one : RappId :=
  ⟨1⟩

def dummy : RappId :=
  ⟨1000000000000000⟩

instance : LT RappId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := RappId) (· < ·) :=
  λ n m => inferInstanceAs $ Decidable (n.toNat < m.toNat)

instance : ToString RappId where
  toString n := toString n.toNat

instance : Hashable RappId where
  hash n := hash n.toNat

end RappId


/-! ## Iterations -/

def Iteration := Nat
  deriving Inhabited

namespace Iteration

@[inline]
private def toNat : Iteration → Nat :=
  id

@[inline]
private def ofNat : Nat → Iteration :=
  id

@[inline]
protected def one : Iteration :=
  ofNat 1

@[inline]
protected def succ (i : Iteration) : Iteration :=
  ofNat $ i.toNat + 1

protected def none : Iteration :=
  ofNat 0

instance : DecidableEq Iteration :=
  inferInstanceAs $ DecidableEq Nat

instance : ToString Iteration :=
  inferInstanceAs $ ToString Nat

instance : LT Iteration :=
  inferInstanceAs $ LT Nat

instance : LE Iteration :=
  inferInstanceAs $ LE Nat

instance : DecidableRel (α := Iteration) (· < ·) :=
  inferInstanceAs $ DecidableRel (α := Nat) (· < ·)

instance : DecidableRel (α := Iteration) (· ≤ ·) :=
  inferInstanceAs $ DecidableRel (α := Nat) (· ≤ ·)

end Iteration


/-! ## The Tree -/

/--
At each point during the search, every node of the tree (goal, rapp or mvar
cluster) is in one of these states:

- `proven`: the node is proven.
- `unprovable`: the node is unprovable, i.e. it will never be proven regardless
  of any future expansions that might be performed.
- `unknown`: neither of the above.

Every node starts in the `unknown` state and may later become either `proven` or
`unprovable`. After this, the state does not change any more.
-/
inductive NodeState
  | unknown
  | proven
  | unprovable
  deriving Inhabited, BEq

namespace NodeState

instance : ToString NodeState where
  toString
    | unknown => "unknown"
    | proven => "proven"
    | unprovable => "unprovable"

def isUnknown : NodeState → Bool
  | unknown => true
  | _ => false

def isProven : NodeState → Bool
  | proven => true
  | _ => false

def isUnprovable : NodeState → Bool
  | unprovable => true
  | _ => false

def isIrrelevant : NodeState → Bool
  | proven => true
  | unprovable => true
  | unknown => false

end NodeState


/--
A refinement of the `NodeState`, distinguishing between goals proven during
normalisation and goals proven by a child rule application.
-/
inductive GoalState
  | unknown
  | provenByRuleApplication
  | provenByNormalization
  | unprovable
  deriving Inhabited, BEq

namespace GoalState

instance : ToString GoalState where
  toString
    | unknown => "unknown"
    | provenByRuleApplication => "provenByRuleApplication"
    | provenByNormalization =>  "provenByNormalization"
    | unprovable => "unprovable"

def isProvenByRuleApplication : GoalState → Bool
  | provenByRuleApplication => true
  | _ => false

def isProvenByNormalization : GoalState → Bool
  | provenByNormalization => true
  | _ => false

def isProven : GoalState → Bool
  | provenByRuleApplication => true
  | provenByNormalization => true
  | _ => false

def isUnprovable : GoalState → Bool
  | unprovable => true
  | _ => false

def isUnknown : GoalState → Bool
  | unknown => true
  | _ => false

def toNodeState : GoalState → NodeState
  | unknown => NodeState.unknown
  | provenByRuleApplication => NodeState.proven
  | provenByNormalization => NodeState.proven
  | unprovable => NodeState.unprovable

def isIrrelevant (s : GoalState) : Bool :=
  s.toNodeState.isIrrelevant

end GoalState


inductive NormalizationState
  | notNormal
  | normal (postGoal : MVarId) (postState : Meta.SavedState)
  | provenByNormalization (postState : Meta.SavedState)
  deriving Inhabited

namespace NormalizationState

def isNormal : NormalizationState → Bool
  | notNormal => false
  | normal .. => true
  | provenByNormalization .. => true

def isProvenByNormalization : NormalizationState → Bool
  | provenByNormalization .. => true
  | _ => false

end NormalizationState


/--
A goal `G` can be added to the tree for three reasons:

1. `G` was produced by its parent rule as a subgoal. This is the most common
   reason.
2. `G` was copied because it contains some metavariables which were assigned by
   its parent rule. In this case, we record goal of which `G` is a copy. We also
   record the representative of the equivalence class of goals which are copies
   of each other. E.g. if goal `1` is copied to goal `2` and goal `2` is copied
   to goal `3`, they are all part of the equivalence class with representative
   `1`.
-/
inductive GoalOrigin
  | subgoal
  | copied («from» : GoalId) (rep : GoalId)
  | droppedMVar
  deriving Inhabited

namespace GoalOrigin

def originalGoalId? : GoalOrigin → Option GoalId
  | copied _ rep => some rep
  | _ => none

protected def toString : GoalOrigin → String
  | subgoal => "subgoal"
  | copied «from» rep => s!"copy of {«from»}, originally {«rep»}"
  | droppedMVar => "dropped mvar"

end GoalOrigin


structure GoalData (Rapp MVarCluster : Type) : Type where
  id : GoalId
  parent : IO.Ref MVarCluster
  children : Array (IO.Ref Rapp)
  origin : GoalOrigin
  depth : Nat
  state : GoalState
  isIrrelevant : Bool
  isForcedUnprovable : Bool
    -- True if the goal was designated unprovable 'by force'. This happens when
    -- we reach the search depth limit. Any goal beyond this limit becomes
    -- irrelevant and therefore unprovable.
  preNormGoal : MVarId
    -- The goal before normalisation. The goal after normalisation (if any) is
    -- contained in the `normalizationState`.
  normalizationState : NormalizationState
  mvars : Array MVarId
    -- Unassigned expression metavariables that appear in the goal, i.e. that
    -- appear in the target or hypotheses of `goal` when interpreted in the
    -- metavar context of `parent?` (or in the global metavar context if
    -- `parent? = none`).
  successProbability : Percent
  addedInIteration : Iteration
  lastExpandedInIteration : Iteration
    -- Iteration 0 means the node has never been expanded.
  unsafeRulesSelected : Bool
  unsafeQueue : UnsafeQueue
  branchState : BranchState
  failedRapps : Array RegularRule

instance [Nonempty MVarCluster] : Nonempty (GoalData Rapp MVarCluster) :=
  ⟨{ id := default
     parent := Classical.ofNonempty
     children := default
     origin := default
     depth := default
     state := default
     isIrrelevant := default
     isForcedUnprovable := default
     preNormGoal := default
     normalizationState := default
     mvars := default
     successProbability := default
     addedInIteration := default
     lastExpandedInIteration := default
     unsafeRulesSelected := default
     unsafeQueue := default
     branchState := default
     failedRapps := default }⟩


structure MVarClusterData (Goal Rapp : Type) : Type where
  parent? : Option (IO.Ref Rapp)
  goals : Array (IO.Ref Goal)
  isIrrelevant : Bool
  state : NodeState
  deriving Inhabited


structure RappData (Goal MVarCluster : Type) : Type where
  id : RappId
  parent : IO.Ref Goal
  children : Array (IO.Ref MVarCluster)
  state : NodeState
  isIrrelevant : Bool
  appliedRule : RegularRule
  successProbability : Percent
  metaState : Meta.SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  introducedMVars : Array MVarId
    -- Unassigned expression mvars introduced by this rapp. These are exactly
    -- the unassigned expr mvars that are declared in `metaState`, but not in
    -- the meta state of the parent rapp of `parent`.
  assignedMVars : Array MVarId
    -- Expression mvars that were previously unassigned but were assigned by
    -- this rapp. These are exactly the expr mvars that (a) are declared and
    -- unassigned in the meta state of the parent rapp of `parent` and (b) are
    -- assigned in `metaState`.

instance [Nonempty Goal] : Nonempty (RappData Goal MVarCluster) :=
  ⟨{ id := default
     parent := Classical.ofNonempty
     children := default
     state := default
     isIrrelevant := default
     appliedRule := default
     successProbability := default
     metaState := default
     introducedMVars := default
     assignedMVars := default }⟩

mutual
  unsafe inductive GoalUnsafe
    | mk (d : GoalData RappUnsafe MVarClusterUnsafe)

  unsafe inductive MVarClusterUnsafe
    | mk (d : MVarClusterData GoalUnsafe RappUnsafe)

  unsafe inductive RappUnsafe
    | mk (d : RappData GoalUnsafe MVarClusterUnsafe)
end

structure TreeSpec where
  Goal : Type
  Rapp : Type
  MVarCluster : Type
  introGoal : GoalData Rapp MVarCluster → Goal
  elimGoal : Goal → GoalData Rapp MVarCluster
  introRapp : RappData Goal MVarCluster → Rapp
  elimRapp : Rapp → RappData Goal MVarCluster
  introMVarCluster : MVarClusterData Goal Rapp → MVarCluster
  elimMVarCluster : MVarCluster → MVarClusterData Goal Rapp

unsafe def treeImpl : TreeSpec where
  Goal := GoalUnsafe
  Rapp := RappUnsafe
  MVarCluster := MVarClusterUnsafe
  introGoal := GoalUnsafe.mk
  elimGoal | GoalUnsafe.mk x => x
  introRapp := RappUnsafe.mk
  elimRapp | RappUnsafe.mk x => x
  introMVarCluster := MVarClusterUnsafe.mk
  elimMVarCluster | MVarClusterUnsafe.mk x => x

@[implementedBy treeImpl]
opaque tree : TreeSpec := {
  Goal := Unit
  Rapp := Unit
  MVarCluster := Unit
  introGoal := λ _ => default
  elimGoal := λ _ => Classical.ofNonempty
  introRapp := λ _ => default
  elimRapp := λ _ => Classical.ofNonempty
  introMVarCluster := λ _ => default
  elimMVarCluster := λ _ => default
}

def Goal        := tree.Goal
def Rapp        := tree.Rapp
def MVarCluster := tree.MVarCluster

abbrev GoalRef        := IO.Ref Goal
abbrev RappRef        := IO.Ref Rapp
abbrev MVarClusterRef := IO.Ref MVarCluster


namespace MVarCluster

@[inline]
protected def mk : MVarClusterData Goal Rapp → MVarCluster :=
  tree.introMVarCluster

instance : Nonempty MVarCluster :=
  ⟨MVarCluster.mk Classical.ofNonempty⟩

@[inline]
protected def elim : MVarCluster → MVarClusterData Goal Rapp :=
  tree.elimMVarCluster

@[inline]
protected def modify (f : MVarClusterData Goal Rapp → MVarClusterData Goal Rapp)
    (c : MVarCluster) : MVarCluster :=
  MVarCluster.mk $ f $ c.elim

@[inline]
def parent? (c : MVarCluster) : Option RappRef :=
  c.elim.parent?

@[inline]
def setParent (parent? : Option RappRef) (c : MVarCluster) : MVarCluster :=
  c.modify λ c => { c with parent? }

@[inline]
def goals (c : MVarCluster) : Array GoalRef :=
  c.elim.goals

@[inline]
def setGoals (goals : Array GoalRef) (c : MVarCluster) : MVarCluster :=
  c.modify λ c => { c with goals }

@[inline]
def isIrrelevant (c : MVarCluster) : Bool :=
  c.elim.isIrrelevant

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (c : MVarCluster) : MVarCluster :=
  c.modify λ c => { c with isIrrelevant }

@[inline]
def state (c : MVarCluster) : NodeState :=
  c.elim.state

@[inline]
def setState (state : NodeState) (c : MVarCluster) : MVarCluster :=
  c.modify λ c => { c with state }

end MVarCluster


namespace Goal

@[inline]
protected def mk : GoalData Rapp MVarCluster → Goal :=
  tree.introGoal

@[inline]
protected def elim : Goal → GoalData Rapp MVarCluster :=
  tree.elimGoal

@[inline]
protected def modify (f : GoalData Rapp MVarCluster → GoalData Rapp MVarCluster)
    (g : Goal) : Goal :=
  Goal.mk $ f $ g.elim

@[inline]
def id (g : Goal) : GoalId :=
  g.elim.id

@[inline]
def parent (g : Goal) : MVarClusterRef :=
  g.elim.parent

@[inline]
def children (g : Goal) : Array RappRef :=
  g.elim.children

@[inline]
def origin (g : Goal) : GoalOrigin :=
  g.elim.origin

@[inline]
def depth (g : Goal) : Nat :=
  g.elim.depth

@[inline]
def state (g : Goal) : GoalState :=
  g.elim.state

@[inline]
def isIrrelevant (g : Goal) : Bool :=
  g.elim.isIrrelevant

@[inline]
def isForcedUnprovable (g : Goal) : Bool :=
  g.elim.isForcedUnprovable

@[inline]
def preNormGoal (g : Goal) : MVarId :=
  g.elim.preNormGoal

@[inline]
def normalizationState (g : Goal) : NormalizationState :=
  g.elim.normalizationState

@[inline]
def mvars (g : Goal) : Array MVarId :=
  g.elim.mvars

@[inline]
def successProbability (g : Goal) : Percent :=
  g.elim.successProbability

@[inline]
def addedInIteration (g : Goal) : Iteration :=
  g.elim.addedInIteration

@[inline]
def lastExpandedInIteration (g : Goal) : Iteration :=
  g.elim.lastExpandedInIteration

@[inline]
def failedRapps (g : Goal) : Array RegularRule :=
  g.elim.failedRapps

@[inline]
def unsafeRulesSelected (g : Goal) : Bool :=
  g.elim.unsafeRulesSelected

@[inline]
def unsafeQueue (g : Goal) : UnsafeQueue :=
  g.elim.unsafeQueue

@[inline]
def unsafeQueue? (g : Goal) : Option UnsafeQueue :=
  if g.unsafeRulesSelected then some g.unsafeQueue else none

@[inline]
def branchState (g : Goal) : BranchState :=
  g.elim.branchState

@[inline]
def setId (id : GoalId) (g : Goal) : Goal :=
  g.modify λ g => { g with id }

@[inline]
def setParent (parent : MVarClusterRef) (g : Goal) : Goal :=
  g.modify λ g => { g with parent }

@[inline]
def setChildren (children : Array RappRef) (g : Goal) : Goal :=
  g.modify λ g => { g with children }

@[inline]
def setOrigin (origin : GoalOrigin) (g : Goal) : Goal :=
  g.modify λ g => { g with origin }

@[inline]
def setDepth (depth : Nat) (g : Goal) : Goal :=
  g.modify λ g => { g with depth }

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (g : Goal) : Goal :=
  g.modify λ g => { g with isIrrelevant }

@[inline]
def setIsForcedUnprovable (isForcedUnprovable : Bool) (g : Goal) : Goal :=
  g.modify λ g => { g with isForcedUnprovable }

@[inline]
def setPreNormGoal (preNormGoal : MVarId) (g : Goal) : Goal :=
  g.modify λ g => { g with preNormGoal }

@[inline]
def setNormalizationState (normalizationState : NormalizationState) (g : Goal) :
    Goal :=
  g.modify λ g => { g with normalizationState }

@[inline]
def setMVars (mvars : Array MVarId) (g : Goal) : Goal :=
  g.modify λ g => { g with mvars }

@[inline]
def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modify λ g => { g with successProbability }

@[inline]
def setAddedInIteration (addedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify λ g => { g with addedInIteration }

@[inline]
def setLastExpandedInIteration (lastExpandedInIteration : Iteration) (g : Goal) :
    Goal :=
  g.modify λ g => { g with lastExpandedInIteration }

@[inline]
def setUnsafeRulesSelected (unsafeRulesSelected : Bool) (g : Goal) : Goal :=
  g.modify λ g => { g with unsafeRulesSelected }

@[inline]
def setUnsafeQueue (unsafeQueue : UnsafeQueue) (g : Goal) : Goal :=
  g.modify λ g => { g with unsafeQueue }

@[inline]
def setState (state : GoalState) (g : Goal) : Goal :=
  g.modify λ g => { g with state }

@[inline]
def setBranchState (branchState : BranchState) (g : Goal) : Goal :=
  g.modify λ g => { g with branchState }

@[inline]
def setFailedRapps (failedRapps : Array RegularRule) (g : Goal) : Goal :=
  g.modify λ g => { g with failedRapps }

instance : Nonempty Goal :=
  ⟨Goal.mk Classical.ofNonempty⟩

instance : BEq Goal where
  beq g₁ g₂ := g₁.id == g₂.id

instance : Hashable Goal where
  hash g := hash g.id

end Goal


namespace Rapp

@[inline]
protected def mk : RappData Goal MVarCluster → Rapp :=
  tree.introRapp

@[inline]
protected def elim : Rapp → RappData Goal MVarCluster :=
  tree.elimRapp

@[inline]
protected def modify (f : RappData Goal MVarCluster → RappData Goal MVarCluster)
    (r : Rapp) : Rapp :=
  Rapp.mk $ f $ r.elim

@[inline]
def id (r : Rapp) : RappId :=
  r.elim.id

@[inline]
def parent (r : Rapp) : GoalRef :=
  r.elim.parent

@[inline]
def children (r : Rapp) : Array MVarClusterRef :=
  r.elim.children

@[inline]
def state (r : Rapp) : NodeState :=
  r.elim.state

@[inline]
def isIrrelevant (r : Rapp) : Bool :=
  r.elim.isIrrelevant

@[inline]
def appliedRule (r : Rapp) : RegularRule :=
  r.elim.appliedRule

@[inline]
def successProbability (r : Rapp) : Percent :=
  r.elim.successProbability

@[inline]
def metaState (r : Rapp) : Meta.SavedState :=
  r.elim.metaState

@[inline]
def introducedMVars (r : Rapp) : Array MVarId :=
  r.elim.introducedMVars

@[inline]
def assignedMVars (r : Rapp) : Array MVarId :=
  r.elim.assignedMVars

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modify λ r => { r with id }

@[inline]
def setParent (parent : GoalRef) (r : Rapp) : Rapp :=
  r.modify λ r => { r with parent }

@[inline]
def setChildren (children : Array MVarClusterRef) (r : Rapp) : Rapp :=
  r.modify λ r => { r with children }

@[inline]
def setState (state : NodeState) (r : Rapp) : Rapp :=
  r.modify λ r => { r with state }

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (r : Rapp) : Rapp :=
  r.modify λ r => { r with isIrrelevant }

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : Rapp) : Rapp :=
  r.modify λ r => { r with appliedRule }

@[inline]
def setSuccessProbability (successProbability : Percent) (r : Rapp) : Rapp :=
  r.modify λ r => { r with successProbability }

@[inline]
def setMetaState (metaState : Meta.SavedState) (r : Rapp) : Rapp :=
  r.modify λ r => { r with metaState }

@[inline]
def setIntroducetMVars (introducedMVars : Array MVarId)
    (r : Rapp) : Rapp :=
  r.modify λ r => { r with introducedMVars }

@[inline]
def setAssignedMVars (assignedMVars : Array MVarId) (r : Rapp) : Rapp :=
  r.modify λ r => { r with assignedMVars }

instance : Nonempty Rapp :=
  ⟨Rapp.mk Classical.ofNonempty⟩

instance : BEq Rapp where
  beq r₁ r₂ := r₁.id == r₂.id

instance : Hashable Rapp where
  hash r := hash r.id

end Rapp


/-! ## Miscellaneous Queries -/

namespace Goal

@[inline]
def postNormGoalAndMetaState? (g : Goal) : Option (MVarId × Meta.SavedState) :=
  match g.normalizationState with
  | NormalizationState.normal postGoal postState => some (postGoal, postState)
  | _ => none

def postNormGoal? (g : Goal) : Option MVarId :=
  g.postNormGoalAndMetaState?.map (·.fst)

def currentGoal (g : Goal) : MVarId :=
  g.postNormGoal?.getD g.preNormGoal

def parentRapp? (g : Goal) : BaseIO (Option RappRef) :=
  return (← g.parent.get).parent?

def parentMetaState (g : Goal) : MetaM Meta.SavedState := do
  match ← g.parentRapp? with
  | none => saveState
  | some parent => return (← parent.get).metaState

def currentGoalAndMetaState (g : Goal) : MetaM (MVarId × Meta.SavedState) :=
  match g.postNormGoalAndMetaState? with
  | some x => return x
  | none => return (g.preNormGoal, ← g.parentMetaState)

def isUnsafeExhausted (g : Goal) : Bool :=
  g.unsafeRulesSelected && g.unsafeQueue.isEmpty

def isExhausted (g : Goal) : BaseIO Bool :=
  pure g.isUnsafeExhausted <||>
  g.children.anyM λ rref =>
    return (← rref.get).appliedRule.isSafe

def isActive (g : Goal) : BaseIO Bool :=
  return ! (← pure g.isIrrelevant <||> g.isExhausted)

def hasProvableRapp (g : Goal) : BaseIO Bool :=
  g.children.anyM λ r => return ! (← r.get).state.isUnprovable

def firstProvenRapp? (g : Goal) : BaseIO (Option RappRef) :=
  g.children.findSomeM? λ rref =>
    return if (← rref.get).state.isProven then some rref else none

def hasMVar (g : Goal) : Bool :=
  ! g.mvars.isEmpty

def priority (g : Goal) : Percent :=
  g.successProbability * unificationGoalPenalty ^ g.mvars.size

def isNormal (g : Goal) : Bool :=
  g.normalizationState.isNormal

def originalGoalId (g : Goal) : GoalId :=
  g.origin.originalGoalId?.getD g.id

end Goal


namespace Rapp

def introducesMVar (r : Rapp) : Bool :=
  ! r.introducedMVars.isEmpty

def parentPostNormMetaState (r : Rapp) : MetaM Meta.SavedState := do
  (← r.parent.get).parentMetaState

def foldSubgoalsM [Monad m] [MonadLiftT (ST IO.RealWorld) m] (init : σ)
    (f : σ → GoalRef → m σ) (r : Rapp) : m σ :=
  r.children.foldlM (init := init) λ s cref => do
    (← cref.get).goals.foldlM (init := s) f

def forSubgoalsM [Monad m] [MonadLiftT (ST IO.RealWorld) m]
    (f : GoalRef → m Unit) (r : Rapp) : m Unit :=
  r.children.forM λ cref => do (← cref.get).goals.forM f

def depth (r : Rapp) : BaseIO Nat :=
  return (← r.parent.get).depth

end Rapp
