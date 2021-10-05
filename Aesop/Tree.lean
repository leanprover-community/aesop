/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Check
import Aesop.Tree.BranchState
import Aesop.Tree.MutAltTree
import Aesop.Tree.UnsafeQueue
import Aesop.Rule
import Aesop.Util
import Aesop.Tracing
import Std

open Lean
open Lean.Meta
open Std

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadError m]

@[inlineIfReduce]
private def Bool.toYesNo : Bool → Format
  | true => "yes"
  | false => "no "

namespace Aesop

/-! ## Node IDs -/

-- TODO This could be a performance issue. If so, change `Nat` to `USize` and
-- maybe remove the `structure` wrapper to ensure unboxing.
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


/-! ## Goal Nodes and Rule Applications -/

/--
At each point during the search, a goal is in one of these states:

- `active`: the goal is not proven, but not all rules that can be applied to
  it have been applied yet.
- `inactive`: all rules that can be applied to the goal have been applied, but
  some of its rule applications may be provable.
- `provenByRuleApplication`: the goal has a child rapp that is proven.
- `provenByNormalization`: the goal was proven during normalization.
- `unprovable`: all rules that can be applied to the goal have been applied, but
  all resulting rapps are unprovable.
- `irrelevant`: the goal goal's parent rapp is already unprovable (or itself
  irrelevant).

A goal starts as active. It may then become inactive if we exhaust all its rules
without determining whether it is provable or unprovable. Eventually it becomes
either proven, unprovable or irrelevant, after which its state does not
change any more.
-/
inductive GoalState
  | active
  | inactive
  | provenByRuleApplication
  | provenByNormalization
  | unprovable
  | irrelevant
  deriving Inhabited, BEq

namespace GoalState

instance : ToString GoalState where
  toString
    | active => "active"
    | inactive => "inactive"
    | provenByRuleApplication => "provenByRuleApplication"
    | provenByNormalization =>  "provenByNormalization"
    | unprovable => "unprovable"
    | irrelevant => "irrelevant"

def isProvenByRuleApplication : GoalState → Bool
  | provenByRuleApplication => true
  | _ => false

def isProvenByNormalization : GoalState → Bool
  | provenByNormalization => true
  | _ => false

def isUnprovable : GoalState → Bool
  | unprovable => true
  | _ => false

def isIrrelevant : GoalState → Bool
  | irrelevant => true
  | _ => false

def isActive : GoalState → Bool
  | active => true
  | _ => false

def isInactive : GoalState → Bool
  | inactive => true
  | _ => false

def isProven : GoalState → Bool
  | provenByRuleApplication => true
  | provenByNormalization => true
  | _ => false

end GoalState


-- Invariant: if proofStatus = provenByNormalization then isNormal = true
-- Invariant: All goal IDs in a tree are distinct.
-- Invariant: The goal ID of a node is smaller than the goal IDs of its
--   descendant goals.
structure GoalData' (GoalData RappData : Type) : Type where
  id : GoalId
  goal : MVarId
  successProbability : Percent
  addedInIteration : Iteration
  lastExpandedInIteration : Iteration
    -- Iteration 0 means the node has never been expanded.
  state : GoalState
  isNormal : Bool
  unsafeRulesSelected : Bool
  unsafeQueue : UnsafeQueue
  branchState : BranchState
  failedRapps : Array RegularRule
  deferTo : Option (IO.Ref (MutAltTree IO.RealWorld GoalData RappData))
  deriving Inhabited


/--
At each point during the search, a rapp is in one of these states:

- `active`: none of the below conditions apply.
- `proven`: all the rapp's child goals have been proven.
- `unprovable`: one of the rapp's child goals is unprovable.
- `irrelevant`: the rapp's parent goal is already proven (or itself irrelevant).

A rapp starts in the active state. It eventually becomes either proven,
unprovable or irrelevant, after which its state does not change any more.
-/
inductive RappState
  | active
  | proven
  | unprovable
  | irrelevant
  deriving Inhabited, BEq

namespace RappState

instance : ToString RappState where
  toString
    | active => "active"
    | proven => "proven"
    | unprovable => "unprovable"
    | irrelevant => "irrelevant"

def isProven : RappState → Bool
  | proven => true
  | _ => false

def isUnprovable : RappState → Bool
  | unprovable => true
  | _ => false

def isIrrelevant : RappState → Bool
  | irrelevant => true
  | _ => false

def isActive : RappState → Bool
  | active => true
  | _ => false

end RappState


-- Workaround for a compiler bug. If we inline this definition, the nested
-- inductive compiler fails on `GoalDataUnsafe`.
private abbrev UnificationGoalOriginsMap α := PersistentHashMap MVarId α

-- Invariant: All rapp IDs in a tree are distinct.
-- Invariant: The rapp ID of a node is smaller than the rapp IDs of its
--   descendant rapps.
-- Invariant: The mvars in `unificationGoalOrigins` are declared but unassigned
--   in `state`.
-- Invariant: The rapps referenced by `unificationGoalOrigins` are ancestors of
--   this rapp.
structure RappData' (GoalData RappData : Type) : Type where
  id : RappId
  depth : Nat -- TODO unused?
  state : RappState
  metaState : Meta.SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  unificationGoalOrigins :
    UnificationGoalOriginsMap (IO.Ref (MutAltTree IO.RealWorld RappData GoalData))
  appliedRule : RegularRule
  successProbability : Percent
  deriving Inhabited

mutual
  unsafe inductive GoalDataUnsafe
    | mk : GoalData' GoalDataUnsafe RappDataUnsafe → GoalDataUnsafe

  unsafe inductive RappDataUnsafe
    | mk : RappData' GoalDataUnsafe RappDataUnsafe → RappDataUnsafe
end

structure GoalRappDataSpec where
  GoalData : Type
  RappData : Type
  introGoalData : GoalData' GoalData RappData → GoalData
  elimGoalData : GoalData → GoalData' GoalData RappData
  introRappData : RappData' GoalData RappData → RappData
  elimRappData : RappData → RappData' GoalData RappData

unsafe def goalRappDataImplUnsafe : GoalRappDataSpec where
  RappData := RappDataUnsafe
  GoalData := GoalDataUnsafe
  introGoalData := GoalDataUnsafe.mk
  elimGoalData | GoalDataUnsafe.mk x => x
  introRappData := RappDataUnsafe.mk
  elimRappData | RappDataUnsafe.mk x => x

@[implementedBy goalRappDataImplUnsafe]
constant goalRappDataImpl : GoalRappDataSpec := {
  GoalData := Unit
  RappData := Unit
  introGoalData := λ _ => arbitrary
  elimGoalData := λ _ => arbitrary
  introRappData := λ _ => arbitrary
  elimRappData := λ _ => arbitrary
}

def GoalData := goalRappDataImpl.GoalData
def RappData := goalRappDataImpl.RappData

abbrev Goal    := MutAltTree IO.RealWorld GoalData RappData
abbrev GoalRef := IO.Ref Goal

abbrev Rapp    := MutAltTree IO.RealWorld RappData GoalData
abbrev RappRef := IO.Ref Rapp


namespace GoalData

@[inline]
def mk : GoalData' GoalData RappData → GoalData :=
  goalRappDataImpl.introGoalData

@[inline]
def elim : GoalData → GoalData' GoalData RappData :=
  goalRappDataImpl.elimGoalData

@[inline]
def modify (f : GoalData' GoalData RappData → GoalData' GoalData RappData)
    (g : GoalData) : GoalData :=
  mk $ f $ elim g

instance : Inhabited GoalData where
  default := mk arbitrary

@[inline]
def id (g : GoalData) : GoalId :=
  g.elim.id

@[inline]
def goal (g : GoalData) : MVarId :=
  g.elim.goal

@[inline]
def successProbability (g : GoalData) : Percent :=
  g.elim.successProbability

@[inline]
def addedInIteration (g : GoalData) : Iteration :=
  g.elim.addedInIteration

@[inline]
def lastExpandedInIteration (g : GoalData) : Iteration :=
  g.elim.lastExpandedInIteration

@[inline]
def deferTo (g : GoalData) : Option GoalRef :=
  g.elim.deferTo

@[inline]
def failedRapps (g : GoalData) : Array RegularRule :=
  g.elim.failedRapps

@[inline]
def unsafeRulesSelected (g : GoalData) : Bool :=
  g.elim.unsafeRulesSelected

@[inline]
def unsafeQueue (g : GoalData) : UnsafeQueue :=
  g.elim.unsafeQueue

@[inline]
def state (g : GoalData) : GoalState :=
  g.elim.state

@[inline]
def isNormal (g : GoalData) : Bool :=
  g.elim.isNormal

@[inline]
def branchState (g : GoalData) : BranchState :=
  g.elim.branchState

@[inline]
def setId (id : GoalId) (g : GoalData) : GoalData :=
  g.modify λ g => { g with id := id }

@[inline]
def setGoal (goal : MVarId) (g : GoalData) : GoalData :=
  g.modify λ g => { g with goal := goal }

@[inline]
def setSuccessProbability (successProbability : Percent) (g : GoalData) :
    GoalData :=
  g.modify λ g => { g with successProbability := successProbability }

@[inline]
def setAddedInIteration (addedInIteration : Iteration) (g : GoalData) :
    GoalData :=
  g.modify λ g => { g with addedInIteration := addedInIteration }

@[inline]
def setLastExpandedInIteration (lastExpandedInIteration : Iteration)
    (g : GoalData) : GoalData :=
  g.modify λ g => { g with lastExpandedInIteration := lastExpandedInIteration }

@[inline]
def setDeferTo (deferTo : Option GoalRef) (g : GoalData) : GoalData :=
  g.modify λ g => { g with deferTo := deferTo }

@[inline]
def setFailedRapps (failedRapps : Array RegularRule) (g : GoalData) : GoalData :=
  g.modify λ g => { g with failedRapps := failedRapps }

@[inline]
def setUnsafeRulesSelected (unsafeRulesSelected : Bool) (g : GoalData) :
    GoalData :=
  g.modify λ g => { g with unsafeRulesSelected := unsafeRulesSelected }

@[inline]
def setUnsafeQueue (unsafeQueue : UnsafeQueue) (g : GoalData) : GoalData :=
  g.modify λ g => { g with unsafeQueue := unsafeQueue }

@[inline]
def setState (state : GoalState) (g : GoalData) : GoalData :=
  g.modify λ g => { g with state := state }

@[inline]
def setNormal (isNormal : Bool) (g : GoalData) : GoalData :=
  g.modify λ g => { g with isNormal := isNormal }

@[inline]
def setBranchState (branchState : BranchState) (g : GoalData) : GoalData :=
  g.modify λ g => { g with branchState := branchState }

open MessageData in
protected def toMessageData (traceMods : TraceModifiers) (g : GoalData) :
    m MessageData := do
  let unsafeQueueLength :=
    if ¬ g.unsafeRulesSelected
      then f!"<not selected>"
      else format g.unsafeQueue.size
  let defersTo ←
    match g.deferTo with
    | none => pure none
    | some deferred =>
      pure m!"deferred in favour of goal {(← deferred.get).payload.id}"
  return m!"Goal {g.id} [{g.successProbability.toHumanString}]" ++ nodeFiltering #[
    m!"Unsafe rules in queue: {unsafeQueueLength}, failed: {g.failedRapps.size}",
    m!"state: {g.state} | normal: {g.isNormal.toYesNo}",
    m!"Iteration added: {g.addedInIteration} | last expanded: {g.lastExpandedInIteration}",
    defersTo,
    if ¬ traceMods.goals then none else
      m!"Goal:{indentD $ ofGoal g.goal}",
    if ¬ traceMods.unsafeQueues || ¬ g.unsafeRulesSelected then none else
      m!"Unsafe queue:{node $ g.unsafeQueue.toArray.map toMessageData}",
    if ¬ traceMods.failedRapps then none else
      m!"Failed rule applications:{node $ g.failedRapps.map toMessageData}" ]

protected def mkInitial (id : GoalId) (goal : MVarId)
    (successProbability : Percent) (addedInIteration : Iteration)
    (branchState : BranchState) : GoalData :=
  mk {
    id := id
    goal := goal
    addedInIteration := addedInIteration
    lastExpandedInIteration := Iteration.none
    deferTo := none
    successProbability := successProbability
    failedRapps := #[]
    unsafeQueue := UnsafeQueue.initial #[]
    state := GoalState.active
    isNormal := false
    unsafeRulesSelected := false
    branchState := branchState
  }

end GoalData


namespace RappData

@[inline]
def mk : RappData' GoalData RappData → RappData :=
  goalRappDataImpl.introRappData

@[inline]
def elim : RappData → RappData' GoalData RappData :=
  goalRappDataImpl.elimRappData

@[inline]
def modify (f : RappData' GoalData RappData → RappData' GoalData RappData)
    (r : RappData) : RappData :=
  mk $ f $ elim r

instance : Inhabited RappData where
  default := mk arbitrary

@[inline]
def id (r : RappData) : RappId :=
  r.elim.id

def depth (r : RappData) : Nat :=
  r.elim.depth

@[inline]
def metaState (r : RappData) : Meta.SavedState :=
  r.elim.metaState

@[inline]
def unificationGoalOrigins (r : RappData) : PersistentHashMap MVarId RappRef :=
  r.elim.unificationGoalOrigins

@[inline]
def appliedRule (r : RappData) : RegularRule :=
  r.elim.appliedRule

@[inline]
def successProbability (r : RappData) : Percent :=
  r.elim.successProbability

@[inline]
def state (r : RappData) : RappState :=
  r.elim.state

@[inline]
def setId (id : RappId) (r : RappData) : RappData :=
  r.modify λ r => { r with id := id }

@[inline]
def setDepth (depth : Nat) (r : RappData) : RappData :=
  r.modify λ r => { r with depth := depth }

@[inline]
def setMetaState (metaState : Meta.SavedState) (r : RappData) : RappData :=
  r.modify λ r => { r with metaState := metaState }

@[inline]
def setUnificationGoalOrigins
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) (r : RappData) :
    RappData :=
  r.modify λ r => { r with unificationGoalOrigins := unificationGoalOrigins }

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : RappData) : RappData :=
  r.modify λ r => { r with appliedRule := appliedRule }

@[inline]
def setSuccessProbability (successProbability : Percent) (r : RappData) :
    RappData :=
  r.modify λ r => { r with successProbability := successProbability }

@[inline]
def setState (state : RappState) (r : RappData) : RappData :=
  r.modify λ r => { r with state := state }

open MessageData in
protected def toMessageData (traceMods : TraceModifiers) (r : RappData) :
    m MessageData := do
  let unificationGoalOrigins : Option MessageData ←
    if ¬ traceMods.unificationGoals || r.unificationGoalOrigins.isEmpty
      then pure none
      else do
        let origins ← r.unificationGoalOrigins.toList.mapM $ λ (mvarId, rref) =>
          return (mkMVar mvarId, (← rref.get).payload.id)
        pure $ some $ m!"unification goals:" ++ node #[toMessageData origins]
  return m!"Rapp {r.id} [{r.successProbability.toHumanString}]" ++
    nodeFiltering #[
      toMessageData r.appliedRule,
      m!"state: {r.state}",
      unificationGoalOrigins ]

protected def mkInitial (id : RappId) (depth : Nat) (metaState : Meta.SavedState)
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef)
    (appliedRule : RegularRule) (successProbability : Percent) : RappData := mk
  { id := id
    depth := depth
    metaState := metaState
    unificationGoalOrigins := unificationGoalOrigins
    appliedRule := appliedRule
    successProbability := successProbability
    state := RappState.active }

end RappData


/-! ## Functions on Goals -/

namespace Goal

/-! ### Constructors -/

@[inline]
protected def mk (parent : Option RappRef) (rapps : Array RappRef)
    (data : GoalData) : Goal :=
  MutAltTree.mk data parent rapps

/-! ### Getters -/

@[inline]
def rapps (g : Goal) : Array RappRef :=
  g.children

@[inline]
def id (g : Goal) : GoalId :=
  g.payload.id

@[inline]
def goal (g : Goal) : MVarId :=
  g.payload.goal

@[inline]
def successProbability (g : Goal) : Percent :=
  g.payload.successProbability

@[inline]
def addedInIteration (g : Goal) : Iteration :=
  g.payload.addedInIteration

@[inline]
def lastExpandedInIteration (g : Goal) : Iteration :=
  g.payload.lastExpandedInIteration

@[inline]
def deferTo (g : Goal) : Option GoalRef :=
  g.payload.deferTo

@[inline]
def failedRapps (g : Goal) : Array RegularRule :=
  g.payload.failedRapps

@[inline]
def unsafeRulesSelected (g : Goal) : Bool :=
  g.payload.unsafeRulesSelected

@[inline]
def unsafeQueue (g : Goal) : UnsafeQueue :=
  g.payload.unsafeQueue

@[inline]
def unsafeQueue? (g : Goal) : Option UnsafeQueue :=
  if g.unsafeRulesSelected then some g.unsafeQueue else none

@[inline]
def state (g : Goal) : GoalState :=
  g.payload.state

@[inline]
def isNormal (g : Goal) : Bool :=
  g.payload.isNormal

@[inline]
def branchState (g : Goal) : BranchState :=
  g.payload.branchState

/-! ### Setters -/

@[inline]
def setId (id : GoalId) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setId id

@[inline]
def setGoal (goal : MVarId) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setGoal goal

@[inline]
def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setSuccessProbability successProbability

@[inline]
def setAddedInIteration (addedInIteration : Iteration) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setAddedInIteration addedInIteration

@[inline]
def setLastExpandedInIteration (lastExpandedInIteration : Iteration) (g : Goal) :
    Goal :=
  g.modifyPayload λ d => d.setLastExpandedInIteration lastExpandedInIteration

@[inline]
def setDeferTo (deferTo : Option GoalRef) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setDeferTo deferTo

@[inline]
def setFailedRapps (failedRapps : Array RegularRule) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setFailedRapps failedRapps

@[inline]
def setUnsafeRulesSelected (unsafeRulesSelected : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setUnsafeRulesSelected unsafeRulesSelected

@[inline]
def setUnsafeQueue (unsafeQueue : UnsafeQueue) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setUnsafeQueue unsafeQueue

@[inline]
def setState (state : GoalState) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setState state

@[inline]
def setNormal (isNormal : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setNormal isNormal

@[inline]
def setBranchState (branchState : BranchState) (g : Goal) : Goal :=
  g.modifyPayload λ d => d.setBranchState branchState

/-! ### Miscellaneous -/

def hasNoUnexpandedUnsafeRule (g : Goal) : Bool :=
  if ¬ g.unsafeRulesSelected
    then false
    else g.unsafeQueue.isEmpty

end Goal


/-! ## Functions on Rule Applications -/

namespace Rapp

/-! ### Constructors -/

@[inline]
protected def mk (parent : Option GoalRef) (subgoals : Array GoalRef)
    (data : RappData) : Rapp :=
  MutAltTree.mk data parent subgoals

/-! ### Getters -/

@[inline]
def parent! (r : Rapp) : GoalRef :=
  match r.parent with
  | some p => p
  | none => panic! s!"aesop/Rapp.parent!: rapp {r.payload.id} "

@[inline]
def subgoals (r : Rapp) : Array GoalRef :=
  r.children

@[inline]
def id (r : Rapp) : RappId :=
  r.payload.id

@[inline]
def depth (r : Rapp) : Nat :=
  r.payload.depth

@[inline]
def metaState (r : Rapp) : Meta.SavedState :=
  r.payload.metaState

@[inline]
def unificationGoalOrigins (r : Rapp) : PersistentHashMap MVarId RappRef :=
  r.payload.unificationGoalOrigins

@[inline]
def appliedRule (r : Rapp) : RegularRule :=
  r.payload.appliedRule

@[inline]
def successProbability (r : Rapp) : Percent :=
  r.payload.successProbability

@[inline]
def state (r : Rapp) : RappState :=
  r.payload.state

-- Setters

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setId id

@[inline]
def setMetaState (metaState : Meta.SavedState) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setMetaState metaState

@[inline]
def setDepth (depth : Nat) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setDepth depth

@[inline]
def setUnificationGoalOrigins
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) (r : Rapp) :
    Rapp :=
  r.modifyPayload λ r => r.setUnificationGoalOrigins unificationGoalOrigins

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setAppliedRule appliedRule

@[inline]
def setSuccessProbability (successProbability : Percent) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setSuccessProbability successProbability

@[inline]
def setState (state : RappState) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setState state

end Rapp


/-! ### Running MetaM Actions in Rapp States -/

-- The following functions let us run MetaM actions in the context of a rapp or
-- goal. Rapps save the metavariable context in which they were run by storing a
-- `Meta.SavedState`. When we, for example, apply a rule to a goal, we run the
-- rule's action in the metavariable context of the goal (which is the
-- metavariable context of the goal's parent rapp). The resulting metavariable
-- context, in which the goal mvar is assigned to an expression generated by the
-- rule, then becomes the metavariable context of the rule's rapp.
--
-- To save and restore metavariable contexts, we use the `MonadBacktrack MetaM`
-- instance. This means that some elements of the state are persistent, notably
-- caches and trace messages. These become part of the global state.
--
-- The environment is not persistent. This means that modifications of the
-- environment made by a rule are not visible in the global state and are reset
-- once the tactic exits. As a result, rules which modify the environment are
-- likely to fail.

@[inline]
def Rapp.runMetaM (x : MetaM α) (r : Rapp) : MetaM (α × Meta.SavedState) :=
  runMetaMInSavedState r.metaState x

@[inline]
def Rapp.runMetaMModifying (x : MetaM α) (r : Rapp) : MetaM (α × Rapp) := do
  let (result, finalState) ← r.runMetaM x
  return (result, r |>.setMetaState finalState)

@[inline]
def RappRef.runMetaM (x : MetaM α) (rref : RappRef) :
    MetaM (α × Meta.SavedState) := do
  (← rref.get).runMetaM x

@[inline]
def RappRef.runMetaMModifying (x : MetaM α) (rref : RappRef) : MetaM α := do
  let (result, r) ← (← rref.get).runMetaMModifying x
  rref.set r
  return result

def Goal.runMetaMInParentState (x : MetaM α) (g : Goal) :
    MetaM (α × Meta.SavedState) :=
  match g.parent with
  | none => runMetaMObservingFinalState x
  | some rref => RappRef.runMetaM x rref

def Goal.runMetaMModifyingParentState (x : MetaM α) (g : Goal) :
    MetaM α :=
  match g.parent with
  | none => x
  | some rref => RappRef.runMetaMModifying x rref

@[inline]
def GoalRef.runMetaMInParentState (x : MetaM α) (gref : GoalRef) :
    MetaM (α × Meta.SavedState) := do
  (← gref.get).runMetaMInParentState x

@[inline]
def GoalRef.runMetaMModifyingParentState (x : MetaM α) (gref : GoalRef) :
    MetaM α := do
  (← gref.get).runMetaMModifyingParentState x


/-! ## Formatting -/

def Goal.toMessageData (traceMods : TraceModifiers) (g : Goal) :
    MetaM MessageData :=
  match g.parent with
  | none => g.payload.toMessageData traceMods
  | some (rref : RappRef) => do
    let (res, _) ← rref.runMetaM do
      addMessageContext (← g.payload.toMessageData traceMods)
    return res

def GoalRef.toMessageData (traceMods : TraceModifiers) (gref : GoalRef) :
    MetaM MessageData := do
  (← gref.get).toMessageData traceMods

def Rapp.toMessageData (traceMods : TraceModifiers) (r : Rapp) :
    MetaM MessageData := do
  let (res, _) ← r.runMetaM do
    addMessageContext (← r.payload.toMessageData traceMods)
  return res

def RappRef.toMessageData (traceMods : TraceModifiers) (rref : RappRef) :
    MetaM MessageData := do
  (← rref.get).toMessageData traceMods

def nodeMessageSeparator : MessageData :=
  m!"-*-*-*-*-*-\n"

mutual
  private partial def goalTreeToMessageData (traceMods : TraceModifiers)
      (goal : Goal) : MetaM MessageData := do
    let goalMsg ← goal.toMessageData traceMods
    let childrenMsgs ← goal.rapps.mapM λ c => do
      rappTreeToMessageData traceMods (← c.get)
    return nodeMessageSeparator ++ goalMsg ++ MessageData.node childrenMsgs

  private partial def rappTreeToMessageData (traceMods : TraceModifiers)
      (rapp : Rapp) : MetaM MessageData := do
    let rappMsg ← rapp.toMessageData traceMods
    let childrenMsgs ← rapp.subgoals.mapM λ c => do
      goalTreeToMessageData traceMods (← c.get)
    return nodeMessageSeparator ++ rappMsg ++ MessageData.node childrenMsgs
end

def Goal.treeToMessageData (traceMods : TraceModifiers) (g : Goal) :
    MetaM MessageData :=
  goalTreeToMessageData traceMods g

def GoalRef.treeToMessageData (traceMods : TraceModifiers) (gref : GoalRef) :
    MetaM MessageData := do
  (← gref.get).treeToMessageData traceMods

def Rapp.treeToMessageData (traceMods : TraceModifiers) (r : Rapp) :
    MetaM MessageData := do
  rappTreeToMessageData traceMods r

def RappRef.treeToMessageData (traceMods : TraceModifiers) (rref : RappRef) :
    MetaM MessageData := do
  (← rref.get).treeToMessageData traceMods


/-! ## Miscellaneous Functions -/

namespace Goal

def mayHaveUnexpandedRapp (g : Goal) : m Bool := do pure $
  ¬ g.hasNoUnexpandedUnsafeRule ∧
  ¬ (← g.rapps.anyM λ r => return (← r.get : Rapp).appliedRule.isSafe)

def hasProvableRapp (g : Goal) : m Bool :=
  g.rapps.anyM λ r => return ¬ (← r.get).state.isUnprovable

def isUnprovableNoCache (g : Goal) : m Bool :=
  notM (g.mayHaveUnexpandedRapp <||> g.hasProvableRapp)

def firstProvenRapp? (g : Goal) : m (Option RappRef) :=
  g.rapps.findSomeM? λ rref =>
    return if (← rref.get).state.isProven then some rref else none

def unificationGoalOrigins (g : Goal) : m (PersistentHashMap MVarId RappRef) :=
  match g.parent with
  | some rref => return Rapp.unificationGoalOrigins (← rref.get)
  | none => return PersistentHashMap.empty

-- TODO This is overly coarse. Even if the parent rapp has unification goals,
-- they need not appear in this goal.
def hasUnificationGoal (g : Goal) : m Bool :=
  return ! (← g.unificationGoalOrigins).isEmpty

def parentDepth (g : Goal) : m Nat :=
  match g.parent with
  | none => pure 0
  | some rref => return Rapp.depth (← rref.get)

end Goal


namespace Rapp

def hasUnificationGoal (r : Rapp) : Bool :=
  ! r.unificationGoalOrigins.isEmpty

def isUnprovableNoCache (r : Rapp) : m Bool :=
  r.subgoals.anyM λ subgoal => return (← subgoal.get).state.isUnprovable

def isProvenNoCache (r : Rapp) : m Bool :=
  r.subgoals.allM λ subgoal => return (← subgoal.get).state.isProven

end Rapp


private def findActiveDescendantGoalCore (x : Sum GoalRef RappRef) :
    m (Option GoalRef) := do
  let result : IO.Ref (Option GoalRef) ← ST.mkRef none
  MATRef.visitDown'
    (λ gref : GoalRef => do
      if (← gref.get).state.isActive then
        result.set gref
        return false
      else
        return true)
    (λ rref : RappRef => return true)
    x
  result.get

def GoalRef.findActiveDescendantGoal : GoalRef → m (Option GoalRef) :=
  findActiveDescendantGoalCore ∘ Sum.inl

def RappRef.findActiveDescendantGoal : RappRef → m (Option GoalRef) :=
  findActiveDescendantGoalCore ∘ Sum.inr


/-! ## Propagating Provability/Unprovability/Irrelevance -/

@[inline]
def setIrrelevantCore : Sum GoalRef RappRef → m Unit :=
  MATRef.visitDown'
    (λ gref : GoalRef => do
      if (← gref.get).state.isIrrelevant
        then return false -- Subtree should already be marked as irrelevant.
        else do
          gref.modify λ g => g.setState GoalState.irrelevant
          return true)
    (λ rref : RappRef => do
      if (← rref.get).state.isIrrelevant
        then return false
        else do
          rref.modify λ r => r.setState RappState.irrelevant
          return true)

def GoalRef.setIrrelevant : GoalRef → m Unit :=
  setIrrelevantCore ∘ Sum.inl

def RappRef.setIrrelevant : RappRef → m Unit :=
  setIrrelevantCore ∘ Sum.inr

private def setRappProvenAndSiblingsIrrelevant (rref : RappRef) : m Unit := do
  rref.modify λ r => r.setState RappState.proven
  (← MATRef.siblings rref).forM RappRef.setIrrelevant

@[inline]
def setProvenCore : Sum GoalRef RappRef → m Unit :=
  MATRef.visitUp'
    -- Goals are unconditionally marked as proven.
    (λ gref : GoalRef => do
      gref.modify λ g => g.setState GoalState.provenByRuleApplication
      return true)
    -- Rapps are marked as proven only if they are in fact proven, i.e. if all
    -- their subgoals are (marked as) proven. In this case, we also need to
    -- mark siblings of the rapp (and their descendants) as irrelevant.
    (λ rref : RappRef => do
      if ← notM (← rref.get).isProvenNoCache
        then pure false
        else setRappProvenAndSiblingsIrrelevant rref *> pure true)

private def GoalRef.setProven (firstGoalState : GoalState) (gref : GoalRef) :
    m Unit := do
  let g ← gref.get
  gref.set $ g.setState firstGoalState
  match g.parent with
  | none => return ()
  | some parent => setProvenCore $ Sum.inr parent

def GoalRef.setProvenByRuleApplication (gref : GoalRef) : m Unit :=
  gref.setProven (firstGoalState := GoalState.provenByRuleApplication)

def GoalRef.setProvenByNormalization (gref : GoalRef) : m Unit :=
  gref.setProven (firstGoalState := GoalState.provenByNormalization)

def RappRef.setProven (firstRappUnconditional : Bool) (rref : RappRef) :
    m Unit := do
  if firstRappUnconditional then do
    setRappProvenAndSiblingsIrrelevant rref
    setProvenCore $ Sum.inl (← rref.get).parent!
  else
    setProvenCore $ Sum.inr rref

private def setGoalUnprovableAndSiblingsIrrelevant (gref : GoalRef) :
    m Unit := do
  gref.modify λ g => g.setState GoalState.unprovable
  (← MATRef.siblings gref).forM GoalRef.setIrrelevant

@[inline]
def setUnprovableCore : Sum GoalRef RappRef → m Unit :=
  MATRef.visitUp'
    -- Goals are marked as unprovable only if they are in fact unprovable, i.e.
    -- if all their rule applications are unprovable and they do not have
    -- unexpanded rule applications. In this case, we also need to mark
    -- siblings of the goal (and their descendants) as irrelevant.
    (λ gref : GoalRef => do
      let g ← gref.get
      if ← g.isUnprovableNoCache
        then setGoalUnprovableAndSiblingsIrrelevant gref *> return true
        else return false)
    -- Rapps are unconditionally marked as unprovable.
    (λ rref : RappRef => do
      rref.modify λ r => r.setState RappState.unprovable
      return true)

def GoalRef.setUnprovable (firstGoalUnconditional : Bool) (gref : GoalRef) :
    m Unit :=
  if firstGoalUnconditional then do
    setGoalUnprovableAndSiblingsIrrelevant gref
    match (← gref.get).parent with
    | none => return ()
    | some parent => setUnprovableCore $ Sum.inr parent
  else
    setUnprovableCore $ Sum.inl gref

def RappRef.setUnprovable : RappRef → m Unit :=
  setUnprovableCore ∘ Sum.inr

def GoalRef.setUnprovableUnconditionallyAndSetDescendantsIrrelevant
    (gref : GoalRef) : m Unit := do
  gref.setUnprovable (firstGoalUnconditional := true)
  (← gref.get).children.forM λ rref : RappRef => rref.setIrrelevant

/-! ## Copying Trees -/

namespace TreeCopy

structure Context (m : Type → Type _) where
  -- Hook which is called after a goal has been copied. Receives the old and new
  -- goal. Note: the new goal does not yet have any child rapps when this hook
  -- is called.
  afterAddGoal : GoalRef → GoalRef → m Unit
  -- Hook which is called after a rapp has been copied. Receives the old and new
  -- rapp. Note: the new rapp does not yet have any subgoals when this hook is
  -- called.
  afterAddRapp : RappRef → RappRef → m Unit

structure State where
  nextGoalId : GoalId
  nextRappId : RappId
  goalMap : HashMap GoalId GoalRef
  rappMap : HashMap RappId RappRef

abbrev TreeCopyT m := StateRefT' IO.RealWorld State $ ReaderT (Context m) m

namespace TreeCopyT

def run (ctx : Context m) (s : State) (x : TreeCopyT m α) : m (α × State) :=
  StateRefT'.run x s |>.run ctx

def run' (afterAddGoal : GoalRef → GoalRef → m Unit)
    (afterAddRapp : RappRef → RappRef → m Unit) (nextGoalId : GoalId)
    (nextRappId : RappId) (x : TreeCopyT m α) : m (α × State) :=
  x.run
    { afterAddGoal := afterAddGoal
      afterAddRapp := afterAddRapp }
    { nextGoalId := nextGoalId,
      nextRappId := nextRappId,
      goalMap := HashMap.empty,
      rappMap := HashMap.empty }

instance [AddErrorMessageContext m] : AddErrorMessageContext (TreeCopyT m) where
  add := λ stx msg => liftM (AddErrorMessageContext.add stx msg : m _)

end TreeCopyT

def getAndIncrementNextGoalId : TreeCopyT m GoalId := do
  let s ← get
  let id := s.nextGoalId
  set { s with nextGoalId := id.succ }
  return id

def getAndIncrementNextRappId : TreeCopyT m RappId := do
  let s ← get
  let id := s.nextRappId
  set { s with nextRappId := id.succ }
  return id

def adjustUnificationGoalOrigins
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) :
    TreeCopyT m (PersistentHashMap MVarId RappRef) := do
  let rappMap := (← get).rappMap
  unificationGoalOrigins.mapM λ r => do
    let id := (← r.get).id
    let (some newRappRef) ← rappMap.find? id
      | throwError "aesop/copyTree: internal error: unificationGoalOrigins points to unknown rapp {id}"
    return newRappRef

mutual
  -- Copies `gref` and all its descendants. The copy of `gref` becomes a child
  -- of `parent`. Returns the copy of `gref`.
  partial def copyGoalTree (parent : RappRef) (gref : GoalRef) :
      TreeCopyT m GoalRef := do
    let g ← gref.get
    let newGoalId ← getAndIncrementNextGoalId
    let newGoalRef ← ST.mkRef $
      Goal.mk (some parent) #[] (g.payload.setId newGoalId)
    modify λ s => { s with goalMap := s.goalMap.insert g.id newGoalRef }
    parent.modify λ r => r.addChild newGoalRef
    (← read).afterAddGoal gref newGoalRef
    g.rapps.forM λ rref => discard $ copyRappTree newGoalRef rref
    return newGoalRef

  -- Copies `rref` and all its descendants. The copy of `rref` becomes a child
  -- of `parent`. Returns the copy of `rref`.
  partial def copyRappTree (parent : GoalRef) (rref : RappRef) :
      TreeCopyT m RappRef := do
    let r ← rref.get
    let newRappId ← getAndIncrementNextRappId
    let newRappRef ← ST.mkRef $
      Rapp.mk (some parent) #[] $ r.payload.setId newRappId
    modify λ s => { s with rappMap := s.rappMap.insert r.id newRappRef }
    newRappRef.modifyM λ r =>
      return r.setUnificationGoalOrigins
        (← adjustUnificationGoalOrigins r.unificationGoalOrigins)
    parent.modify λ g => g.addChild newRappRef
    (← read).afterAddRapp rref newRappRef
    r.subgoals.forM λ gref => discard $ copyGoalTree newRappRef gref
    return newRappRef
end

end TreeCopy

def GoalRef.copyTree (afterAddGoal : GoalRef → GoalRef → m Unit)
    (afterAddRapp : RappRef → RappRef → m Unit) (nextGoalId : GoalId)
    (nextRappId : RappId) (parent : RappRef) (gref : GoalRef) :
    m (GoalRef × TreeCopy.State) := do
  TreeCopy.copyGoalTree parent gref |>.run'
    afterAddGoal afterAddRapp nextGoalId nextRappId

def RappRef.copyTree (afterAddGoal : GoalRef → GoalRef → m Unit)
    (afterAddRapp : RappRef → RappRef → m Unit) (nextGoalId : GoalId)
    (nextRappId : RappId) (parent : GoalRef) (rref : RappRef) :
    m (RappRef × TreeCopy.State) := do
  TreeCopy.copyRappTree parent rref |>.run'
    afterAddGoal afterAddRapp nextGoalId nextRappId


/-! ## Checking Invariants -/

namespace CheckIdInvariant

structure Context where
  maxAncestorGoalId : GoalId := GoalId.zero
  maxAncestorRappId : RappId := RappId.zero

structure State where
  visitedGoalIds : HashSet GoalId := HashSet.empty
  visitedRappIds : HashSet RappId := HashSet.empty

abbrev CheckIdInvariantT m :=
  ReaderT CheckIdInvariant.Context $
  StateRefT' IO.RealWorld CheckIdInvariant.State m

namespace CheckIdInvariantT

def run (x : CheckIdInvariantT m α) : m α := do
  let (res, s) ← ReaderT.run x {} |>.run {}
  return res

end CheckIdInvariantT

instance [AddErrorMessageContext m] :
    AddErrorMessageContext (CheckIdInvariantT m) where
  add := λ stx msg => liftM (AddErrorMessageContext.add stx msg : m _)

-- Using a `mutual` block here produces a very weird error when this function
-- is used (transitively) in `BestFirstSearch.lean`. So for now we manually
-- desugar the `mutual` block.
partial def checkIds : Sum GoalRef RappRef → CheckIdInvariantT m Unit
  | Sum.inl gref => do
    let g ← gref.get
    let id := g.id
    if (← get).visitedGoalIds.contains id then throwError
      "{Check.tree.name}: duplicate goal ID: {id}"
    modify λ s => { s with visitedGoalIds := s.visitedGoalIds.insert id }
    let ctx ← read
    if id < ctx.maxAncestorGoalId then throwError
      "{Check.tree.name}: goal ID {id} is smaller than ancestor goal ID {ctx.maxAncestorGoalId}"
    withReader (λ ctx => { ctx with maxAncestorGoalId := id }) $
      g.rapps.forM (checkIds ∘ Sum.inr)
  | Sum.inr rref => do
    let r ← rref.get
    let id := r.id
    if (← get).visitedRappIds.contains id then throwError
      "{Check.tree.name}: duplicate rapp ID: {id}"
    modify λ s => { s with visitedRappIds := s.visitedRappIds.insert id }
    let ctx ← read
    if id < ctx.maxAncestorRappId then throwError
      "{Check.tree.name}: rapp ID {id} is smaller than ancestor rapp ID {ctx.maxAncestorRappId}"
    withReader (λ ctx => { ctx with maxAncestorRappId := id }) $
      r.subgoals.forM (checkIds ∘ Sum.inl)

end CheckIdInvariant

def GoalRef.checkIds (gref : GoalRef) : m Unit :=
  CheckIdInvariant.checkIds (Sum.inl gref) |>.run

def RappRef.checkIds (rref : RappRef) : m Unit :=
  CheckIdInvariant.checkIds (Sum.inr rref) |>.run

mutual
  private partial def checkUnificationGoalOriginsGoal (gref : GoalRef) :
      MetaM Unit := do
    (← gref.get).rapps.forM checkUnificationGoalOriginsRapp

  private partial def checkUnificationGoalOriginsRapp (rref : RappRef) :
      MetaM Unit := do
    let r ← rref.get
    withoutModifyingState do
      restoreState r.metaState
      for (m, _) in r.unificationGoalOrigins do
        let (some _) ← (← getMCtx).findDecl? m | throwError
          "{Check.tree.name}: in rapp {r.id}: unification goal {m.name} is not declared in the metavariable context"
        if (← isExprMVarAssigned m) then throwError
          "{Check.tree.name}: in rapp {r.id}: unification goal {m.name} is assigned"
    r.subgoals.forM checkUnificationGoalOriginsGoal

end

def GoalRef.checkUnificationGoalOrigins : GoalRef → MetaM Unit :=
  checkUnificationGoalOriginsGoal

def RappRef.checkUnificationGoalOrigins : RappRef → MetaM Unit :=
  checkUnificationGoalOriginsRapp

def GoalRef.checkInvariantsIfEnabled (root : GoalRef) : MetaM Unit := do
  let (true) ← Check.tree.isEnabled | return ()
  unless (← MATRef.hasConsistentParentChildLinks root) do
    throwError "{Check.tree.name}: search tree is not properly linked"
  unless (← MATRef.isAcyclic root) do
    throwError "{Check.tree.name}: search tree contains a cycle"
  root.checkIds
  root.checkUnificationGoalOrigins

end Aesop
