/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Check
import Aesop.Constants
import Aesop.Tree.BranchState
import Aesop.Tree.UnsafeQueue
import Aesop.Rule
import Aesop.Util
import Aesop.Tracing
import Std

open Lean
open Lean.Meta
open Std

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadError m]

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
At each point during the search, a goal is in one of these states:

- `active`: the goal is not proven, but not all rules that can be applied to
  it have been applied yet.
- `inactive`: all rules that can be applied to the goal have been applied, but
  some of its rule applications may be provable. (If a safe rule is successfully
  applied to a goal, the goal immediately becomes inactive.)
- `provenByRuleApplication`: the goal has a child rapp that is proven.
- `provenByNormalization`: the goal was proven during normalization.
- `unprovable`: all rules that can be applied to the goal have been applied, but
  all resulting rapps are unprovable.
- `irrelevant`: the goal's parent rapp is already unprovable (or itself
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
structure GoalData (Goal Rapp : Type) : Type where
  id : GoalId
  parent? : Option (IO.Ref Rapp)
  children : Array (IO.Ref Rapp)
  goal : MVarId
  unificationGoals : HashSet MVarId
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
structure RappData (Goal Rapp : Type) : Type where
  id : RappId
  parent : IO.Ref Goal
  children : Array (IO.Ref Goal)
  depth : Nat -- TODO unused?
  state : RappState
  metaState : Meta.SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  unificationGoalOrigins : UnificationGoalOriginsMap (IO.Ref Rapp)
  appliedRule : RegularRule
  successProbability : Percent

instance {Goal Rapp} [Nonempty Goal] :
    Nonempty (RappData Goal Rapp) :=
  ⟨{ id := default
     parent := Classical.ofNonempty
     children := default
     depth := default
     state := default
     metaState := default
     unificationGoalOrigins := default
     appliedRule := default
     successProbability := default }⟩

mutual
  unsafe inductive GoalUnsafe
    | mk : GoalData GoalUnsafe RappUnsafe → GoalUnsafe

  unsafe inductive RappUnsafe
    | mk : RappData GoalUnsafe RappUnsafe → RappUnsafe
end

structure GoalRappSpec where
  Goal : Type
  Rapp : Type
  introGoal : GoalData Goal Rapp → Goal
  elimGoal : Goal → GoalData Goal Rapp
  introRapp : RappData Goal Rapp → Rapp
  elimRapp : Rapp → RappData Goal Rapp

unsafe def goalRappImplUnsafe : GoalRappSpec where
  Goal := GoalUnsafe
  Rapp := RappUnsafe
  introGoal := GoalUnsafe.mk
  elimGoal | GoalUnsafe.mk x => x
  introRapp := RappUnsafe.mk
  elimRapp | RappUnsafe.mk x => x

@[implementedBy goalRappImplUnsafe]
constant goalRappImpl : GoalRappSpec := {
  Goal := Unit
  Rapp := Unit
  introGoal := λ _ => default
  elimGoal := λ _ => default
  introRapp := λ _ => default
  elimRapp := λ _ => Classical.ofNonempty
}

def Goal := goalRappImpl.Goal
def Rapp := goalRappImpl.Rapp

abbrev GoalRef := IO.Ref Goal
abbrev RappRef := IO.Ref Rapp


namespace Goal

@[inline]
def mk : GoalData Goal Rapp → Goal :=
  goalRappImpl.introGoal

instance : Inhabited Goal where
  default := Goal.mk default

@[inline]
def elim : Goal → GoalData Goal Rapp :=
  goalRappImpl.elimGoal

@[inline]
def modify (f : GoalData Goal Rapp → GoalData Goal Rapp) (g : Goal) : Goal :=
  mk $ f $ elim g

instance : Inhabited Goal where
  default := mk default

@[inline]
def id (g : Goal) : GoalId :=
  g.elim.id

@[inline]
def parent? (g : Goal) : Option RappRef :=
  g.elim.parent?

@[inline]
def children (g : Goal) : Array RappRef :=
  g.elim.children

@[inline]
def goal (g : Goal) : MVarId :=
  g.elim.goal

@[inline]
def unificationGoals (g : Goal) : HashSet MVarId :=
  g.elim.unificationGoals

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
def state (g : Goal) : GoalState :=
  g.elim.state

@[inline]
def isNormal (g : Goal) : Bool :=
  g.elim.isNormal

@[inline]
def branchState (g : Goal) : BranchState :=
  g.elim.branchState

@[inline]
def setId (id : GoalId) (g : Goal) : Goal :=
  g.modify λ g => { g with id := id }

@[inline]
def setParent (parent? : Option RappRef) (g : Goal) : Goal :=
  g.modify λ g => { g with parent? := parent? }

@[inline]
def setChildren (children : Array RappRef) (g : Goal) : Goal :=
  g.modify λ g => { g with children := children }

@[inline]
def setGoal (goal : MVarId) (g : Goal) : Goal :=
  g.modify λ g => { g with goal := goal }

@[inline]
def setUnificationGoals (unificationGoals : HashSet MVarId) (g : Goal) : Goal :=
  g.modify λ g => { g with unificationGoals := unificationGoals }

@[inline]
def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modify λ g => { g with successProbability := successProbability }

@[inline]
def setAddedInIteration (addedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify λ g => { g with addedInIteration := addedInIteration }

@[inline]
def setLastExpandedInIteration (lastExpandedInIteration : Iteration) (g : Goal) :
    Goal :=
  g.modify λ g => { g with lastExpandedInIteration := lastExpandedInIteration }

@[inline]
def setFailedRapps (failedRapps : Array RegularRule) (g : Goal) : Goal :=
  g.modify λ g => { g with failedRapps := failedRapps }

@[inline]
def setUnsafeRulesSelected (unsafeRulesSelected : Bool) (g : Goal) : Goal :=
  g.modify λ g => { g with unsafeRulesSelected := unsafeRulesSelected }

@[inline]
def setUnsafeQueue (unsafeQueue : UnsafeQueue) (g : Goal) : Goal :=
  g.modify λ g => { g with unsafeQueue := unsafeQueue }

@[inline]
def setState (state : GoalState) (g : Goal) : Goal :=
  g.modify λ g => { g with state := state }

@[inline]
def setNormal (isNormal : Bool) (g : Goal) : Goal :=
  g.modify λ g => { g with isNormal := isNormal }

@[inline]
def setBranchState (branchState : BranchState) (g : Goal) : Goal :=
  g.modify λ g => { g with branchState := branchState }

@[inline]
def addChild (child : RappRef) (g : Goal) : Goal :=
  g.modify λ g => { g with children := g.children.push child }

protected def mkInitial (id : GoalId) (parent? : Option (IO.Ref Rapp))
    (goal : MVarId) (unificationGoals : HashSet MVarId)
    (successProbability : Percent) (addedInIteration : Iteration)
    (branchState : BranchState) : Goal :=
  mk {
    id := id
    parent? := parent?
    children := #[]
    goal := goal
    unificationGoals := unificationGoals
    addedInIteration := addedInIteration
    lastExpandedInIteration := Iteration.none
    successProbability := successProbability
    failedRapps := #[]
    unsafeQueue := UnsafeQueue.initial #[]
    state := GoalState.active
    isNormal := false
    unsafeRulesSelected := false
    branchState := branchState
  }

def hasNoUnexpandedUnsafeRule (g : Goal) : Bool :=
  if ¬ g.unsafeRulesSelected
    then false
    else g.unsafeQueue.isEmpty

end Goal


namespace Rapp

@[inline]
def mk : RappData Goal Rapp → Rapp :=
  goalRappImpl.introRapp

@[inline]
def elim : Rapp → RappData Goal Rapp :=
  goalRappImpl.elimRapp

@[inline]
def modify (f : RappData Goal Rapp → RappData Goal Rapp) (r : Rapp) : Rapp :=
  mk $ f $ elim r

instance : Nonempty Rapp :=
  ⟨mk Classical.ofNonempty⟩

def default : IO Rapp := do
  let parent ← IO.mkRef Inhabited.default
  return mk {
    id := Inhabited.default
    parent := parent
    children := Inhabited.default
    depth := Inhabited.default
    state := Inhabited.default
    metaState := Inhabited.default
    unificationGoalOrigins := Inhabited.default
    appliedRule := Inhabited.default
    successProbability := Inhabited.default
  }

@[inline]
def id (r : Rapp) : RappId :=
  r.elim.id

@[inline]
def parent (r : Rapp) : GoalRef :=
  r.elim.parent

@[inline]
def children (r : Rapp) : Array GoalRef :=
  r.elim.children

def depth (r : Rapp) : Nat :=
  r.elim.depth

@[inline]
def metaState (r : Rapp) : Meta.SavedState :=
  r.elim.metaState

@[inline]
def unificationGoalOrigins (r : Rapp) : PersistentHashMap MVarId RappRef :=
  r.elim.unificationGoalOrigins

@[inline]
def appliedRule (r : Rapp) : RegularRule :=
  r.elim.appliedRule

@[inline]
def successProbability (r : Rapp) : Percent :=
  r.elim.successProbability

@[inline]
def state (r : Rapp) : RappState :=
  r.elim.state

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modify λ r => { r with id := id }

@[inline]
def setParent (parent : GoalRef) (r : Rapp) : Rapp :=
  r.modify λ r => { r with parent := parent }

@[inline]
def setChildren (children : Array GoalRef) (r : Rapp) : Rapp :=
  r.modify λ r => { r with children := children }

@[inline]
def setDepth (depth : Nat) (r : Rapp) : Rapp :=
  r.modify λ r => { r with depth := depth }

@[inline]
def setMetaState (metaState : Meta.SavedState) (r : Rapp) : Rapp :=
  r.modify λ r => { r with metaState := metaState }

@[inline]
def setUnificationGoalOrigins
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef) (r : Rapp) :
    Rapp :=
  r.modify λ r => { r with unificationGoalOrigins := unificationGoalOrigins }

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : Rapp) : Rapp :=
  r.modify λ r => { r with appliedRule := appliedRule }

@[inline]
def setSuccessProbability (successProbability : Percent) (r : Rapp) : Rapp :=
  r.modify λ r => { r with successProbability := successProbability }

@[inline]
def setState (state : RappState) (r : Rapp) : Rapp :=
  r.modify λ r => { r with state := state }

@[inline]
def addChild (child : GoalRef) (r : Rapp) : Rapp :=
  r.modify λ r => { r with children := r.children.push child }

protected def mkInitial (id : RappId) (parent : IO.Ref Goal) (depth : Nat)
    (metaState : Meta.SavedState)
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef)
    (appliedRule : RegularRule) (successProbability : Percent) : Rapp := mk
  { id := id
    parent := parent
    children := #[]
    depth := depth
    metaState := metaState
    unificationGoalOrigins := unificationGoalOrigins
    appliedRule := appliedRule
    successProbability := successProbability
    state := RappState.active }

end Rapp


/-! ### Inhabitation -/

-- References such as `GoalRef` and `RappRef` are not `Inhabited` by default.
-- Indeed the following is a bit iffy because we create global ref cells just to
-- prove inhabitation. But as long as we only ever use them as a 'proposition'
-- that will never actually be used, it should be fine. See discussion at
-- https://github.com/leanprover/lean4/issues/984

initialize GoalRef.default : GoalRef ←
  IO.mkRef default

instance : Inhabited GoalRef where
  default := GoalRef.default

instance : Inhabited (RappData Goal Rapp) where
  default := {
    id := default
    parent := default
    children := default
    depth := default
    state := default
    metaState := default
    unificationGoalOrigins := default
    appliedRule := default
    successProbability := default
  }

instance : Inhabited Rapp where
  default := Rapp.mk default

initialize RappRef.default : RappRef ←
  IO.mkRef default

instance : Inhabited RappRef where
  default := RappRef.default


/-! ### Freeing Trees -/

-- In Lean 4, cylic structures -- such as our trees with their parent pointers
-- -- are not freed automatically. This is because the runtime uses reference
-- counting and a parent node and its child will always have a reference count
-- of at least 1 since they hold references to each other. So in order to
-- free a tree, we must break all the cycles.

mutual
  private partial def freeGoalRef (gref : GoalRef) : IO Unit := do
    gref.modify λ g => g.setParent none
    (← gref.get).children.forM freeRappRef

  private partial def freeRappRef (rref : RappRef) : IO Unit := do
    rref.modify λ r => r.setParent default
    (← rref.get).children.forM freeGoalRef
end

def GoalRef.free := freeGoalRef

def RappRef.free := freeRappRef


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
  match g.parent? with
  | none => runMetaMObservingFinalState x
  | some rref => RappRef.runMetaM x rref

def Goal.runMetaMModifyingParentState (x : MetaM α) (g : Goal) :
    MetaM α :=
  match g.parent? with
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


/-! ## Miscellaneous Queries -/

namespace Goal

def mayHaveUnexpandedRapp (g : Goal) : m Bool := do pure $
  ¬ g.hasNoUnexpandedUnsafeRule ∧
  ¬ (← g.children.anyM λ r => return (← r.get : Rapp).appliedRule.isSafe)

def hasProvableRapp (g : Goal) : m Bool :=
  g.children.anyM λ r => return ¬ (← r.get).state.isUnprovable

def isUnprovableNoCache (g : Goal) : m Bool :=
  notM (g.mayHaveUnexpandedRapp <||> g.hasProvableRapp)

def firstProvenRapp? (g : Goal) : m (Option RappRef) :=
  g.children.findSomeM? λ rref =>
    return if (← rref.get).state.isProven then some rref else none

def unificationGoalOrigins (g : Goal) : m (PersistentHashMap MVarId RappRef) :=
  match g.parent? with
  | some rref => return Rapp.unificationGoalOrigins (← rref.get)
  | none => return PersistentHashMap.empty

def hasUnificationGoal (g : Goal) : Bool :=
  ! g.unificationGoals.isEmpty

def parentDepth (g : Goal) : m Nat :=
  match g.parent? with
  | none => pure 0
  | some rref => return Rapp.depth (← rref.get)

def priority (g : Goal) : Percent :=
  g.successProbability * unificationGoalPenalty ^ g.unificationGoals.size

end Goal


namespace Rapp

def hasUnificationGoal (r : Rapp) : Bool :=
  ! r.unificationGoalOrigins.isEmpty

def isUnprovableNoCache (r : Rapp) : m Bool :=
  r.children.anyM λ subgoal => return (← subgoal.get).state.isUnprovable

def isProvenNoCache (r : Rapp) : m Bool :=
  r.children.allM λ subgoal => return (← subgoal.get).state.isProven

end Rapp


/-! ## Formatting -/

section ToMessageData

open MessageData

protected def Goal.toMessageData (traceMods : TraceModifiers) (g : Goal) :
    MetaM MessageData :=
  match g.parent? with
  | none => go
  | some (rref : RappRef) => do
    Prod.fst <$> rref.runMetaM (addMessageContext (← go))
  where
    go : MetaM MessageData := do
      let unsafeQueueLength :=
        if ¬ g.unsafeRulesSelected
          then f!"<not selected>"
          else format g.unsafeQueue.size
      return m!"Goal {g.id} [{g.priority.toHumanString} / {g.successProbability.toHumanString}]" ++ nodeFiltering #[
        m!"Unsafe rules in queue: {unsafeQueueLength}, failed: {g.failedRapps.size}",
        m!"state: {g.state} | normal: {g.isNormal.toYesNo}",
        m!"Iteration added: {g.addedInIteration} | last expanded: {g.lastExpandedInIteration}",
        if ! traceMods.goals then none else
          m!"Goal:{indentD $ ofGoal g.goal}",
        if ! traceMods.unificationGoals then none else
          m!"Unification goals: {g.unificationGoals.toArray.map (·.name)}",
        if ! traceMods.unsafeQueues || ! g.unsafeRulesSelected then none else
          m!"Unsafe queue:{node $ g.unsafeQueue.toArray.map toMessageData}",
        if ! traceMods.failedRapps then none else
          m!"Failed rule applications:{node $ g.failedRapps.map toMessageData}" ]

protected def GoalRef.toMessageData (traceMods : TraceModifiers)
    (gref : GoalRef) : MetaM MessageData := do
  (← gref.get).toMessageData traceMods

protected def Rapp.toMessageData (traceMods : TraceModifiers) (r : Rapp) :
    MetaM MessageData := do
  Prod.fst <$> r.runMetaM (addMessageContext (← go))
  where
    go : MetaM MessageData := do
      let unificationGoalOrigins : Option MessageData ←
        if ¬ traceMods.unificationGoals || r.unificationGoalOrigins.isEmpty
          then pure none
          else do
            let origins ← r.unificationGoalOrigins.toList.mapM $ λ (mvarId, rref) =>
              return (mkMVar mvarId, (← rref.get).id)
            pure $ some $ m!"unification goals:" ++ node #[toMessageData origins]
      return m!"Rapp {r.id} [{r.successProbability.toHumanString}]" ++
        nodeFiltering #[
          toMessageData r.appliedRule,
          m!"state: {r.state}",
          unificationGoalOrigins ]

protected def RappRef.toMessageData (traceMods : TraceModifiers)
    (rref : RappRef) : MetaM MessageData := do
  (← rref.get).toMessageData traceMods

def nodeMessageSeparator : MessageData :=
  m!"-*-*-*-*-*-\n"

mutual
  private partial def goalTreeToMessageData (traceMods : TraceModifiers)
      (goal : Goal) : MetaM MessageData := do
    let goalMsg ← goal.toMessageData traceMods
    let childrenMsgs ← goal.children.mapM λ c => do
      rappTreeToMessageData traceMods (← c.get)
    return nodeMessageSeparator ++ goalMsg ++ MessageData.node childrenMsgs

  private partial def rappTreeToMessageData (traceMods : TraceModifiers)
      (rapp : Rapp) : MetaM MessageData := do
    let rappMsg ← rapp.toMessageData traceMods
    let childrenMsgs ← rapp.children.mapM λ c => do
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

end ToMessageData


/-! ## Finding Siblings -/

def GoalRef.siblings (gref : GoalRef) : m (Array GoalRef) := do
  let g ← gref.get
  match g.parent? with
  | none => return #[]
  | some parent =>
    (← parent.get).children.filterM λ cref => notM $ cref.ptrEq gref

def RappRef.siblings (rref : RappRef) : m (Array RappRef) := do
  let r ← rref.get
  (← r.parent.get).children.filterM λ cref => notM $ cref.ptrEq rref


/-! ## Generic Traversals -/

partial def traverseDown (visitGoal : GoalRef → m Bool)
    (visitRapp : RappRef → m Bool) : Sum GoalRef RappRef → m Unit
  | Sum.inl gref => do
    let continue? ← visitGoal gref
    if continue? then
      (← gref.get).children.forM $ traverseDown visitGoal visitRapp ∘ Sum.inr
  | Sum.inr rref => do
    let continue? ← visitRapp rref
    if continue? then
      (← rref.get).children.forM $ traverseDown visitGoal visitRapp ∘ Sum.inl

partial def traverseUp (visitGoal : GoalRef → m Bool)
    (visitRapp : RappRef → m Bool) : Sum GoalRef RappRef → m Unit
  | Sum.inl gref => do
    let continue? ← visitGoal gref
    if continue? then
      match (← gref.get).parent? with
      | none => return
      | some parent => traverseUp visitGoal visitRapp $ Sum.inr parent
  | Sum.inr rref => do
    let continue? ← visitRapp rref
    if continue? then
      traverseUp visitGoal visitRapp $ Sum.inl (← rref.get).parent

private def findActiveDescendantGoalCore (x : Sum GoalRef RappRef) :
    m (Option GoalRef) := do
  let result : IO.Ref (Option GoalRef) ← ST.mkRef none
  traverseDown
    (λ gref => do
      if (← gref.get).state.isActive then
        result.set gref
        return false
      else
        return true)
    (λ rref => return true)
    x
  result.get

@[inline]
def GoalRef.findActiveDescendantGoal : GoalRef → m (Option GoalRef) :=
  findActiveDescendantGoalCore ∘ Sum.inl

@[inline]
def RappRef.findActiveDescendantGoal : RappRef → m (Option GoalRef) :=
  findActiveDescendantGoalCore ∘ Sum.inr


/-! ## Propagating Provability/Unprovability/Irrelevance -/

private def setIrrelevantCore : Sum GoalRef RappRef → m Unit :=
  traverseDown
    (λ gref => do
      if (← gref.get).state.isIrrelevant
        then return false -- Subtree should already be marked as irrelevant.
        else do
          gref.modify λ g => g.setState GoalState.irrelevant
          return true)
    (λ rref => do
      if (← rref.get).state.isIrrelevant
        then return false
        else do
          rref.modify λ r => r.setState RappState.irrelevant
          return true)

@[inline]
def GoalRef.setIrrelevant : GoalRef → m Unit :=
  setIrrelevantCore ∘ Sum.inl

@[inline]
def RappRef.setIrrelevant : RappRef → m Unit :=
  setIrrelevantCore ∘ Sum.inr

private def setRappProvenAndSiblingsIrrelevant (rref : RappRef) : m Unit := do
  rref.modify λ r => r.setState RappState.proven
  (← rref.siblings).forM RappRef.setIrrelevant

private def setProvenCore : Sum GoalRef RappRef → m Unit :=
  traverseUp
    -- Goals are unconditionally marked as proven.
    (λ gref => do
      gref.modify λ g => g.setState GoalState.provenByRuleApplication
      return true)
    -- Rapps are marked as proven only if they are in fact proven, i.e. if all
    -- their subgoals are (marked as) proven. In this case, we also need to
    -- mark siblings of the rapp (and their descendants) as irrelevant.
    (λ rref => do
      if ← notM (← rref.get).isProvenNoCache
        then pure false
        else setRappProvenAndSiblingsIrrelevant rref *> pure true)

private def GoalRef.setProven (firstGoalState : GoalState) (gref : GoalRef) :
    m Unit := do
  let g ← gref.get
  gref.set $ g.setState firstGoalState
  match g.parent? with
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
    setProvenCore $ Sum.inl (← rref.get).parent
  else
    setProvenCore $ Sum.inr rref

private def setGoalUnprovableAndSiblingsIrrelevant (gref : GoalRef) :
    m Unit := do
  gref.modify λ g => g.setState GoalState.unprovable
  (← gref.siblings).forM GoalRef.setIrrelevant

def setUnprovableCore : Sum GoalRef RappRef → m Unit :=
  traverseUp
    -- Goals are marked as unprovable only if they are in fact unprovable, i.e.
    -- if all their rule applications are unprovable and they do not have
    -- unexpanded rule applications. In this case, we also need to mark
    -- siblings of the goal (and their descendants) as irrelevant.
    (λ gref => do
      let g ← gref.get
      if ← g.isUnprovableNoCache
        then setGoalUnprovableAndSiblingsIrrelevant gref *> return true
        else return false)
    -- Rapps are unconditionally marked as unprovable.
    (λ rref => do
      rref.modify λ r => r.setState RappState.unprovable
      return true)

def GoalRef.setUnprovable (firstGoalUnconditional : Bool) (gref : GoalRef) :
    m Unit :=
  if firstGoalUnconditional then do
    setGoalUnprovableAndSiblingsIrrelevant gref
    match (← gref.get).parent? with
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
    let (some newRappRef) := rappMap.find? id
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
      g.setParent (some parent)
      |>.setChildren #[]
      |>.setId newGoalId
    modify λ s => { s with goalMap := s.goalMap.insert g.id newGoalRef }
    parent.modify λ r => r.addChild newGoalRef
    (← read).afterAddGoal gref newGoalRef
    g.children.forM λ rref => discard $ copyRappTree newGoalRef rref
    return newGoalRef

  -- Copies `rref` and all its descendants. The copy of `rref` becomes a child
  -- of `parent`. Returns the copy of `rref`.
  partial def copyRappTree (parent : GoalRef) (rref : RappRef) :
      TreeCopyT m RappRef := do
    let newRappId ← getAndIncrementNextRappId
    let r ← rref.get
    let newRappRef ← ST.mkRef $
      r.setParent parent
      |>.setChildren #[]
      |>.setId newRappId
    modify λ s => { s with rappMap := s.rappMap.insert r.id newRappRef }
    newRappRef.modifyM λ r =>
      return r.setUnificationGoalOrigins
        (← adjustUnificationGoalOrigins r.unificationGoalOrigins)
    parent.modify λ g => g.addChild newRappRef
    (← read).afterAddRapp rref newRappRef
    r.children.forM λ gref => discard $ copyGoalTree newRappRef gref
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
private partial def checkIds : Sum GoalRef RappRef → CheckIdInvariantT m Unit
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
      g.children.forM (checkIds ∘ Sum.inr)
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
      r.children.forM (checkIds ∘ Sum.inl)

end CheckIdInvariant

def GoalRef.checkIds (gref : GoalRef) : m Unit :=
  CheckIdInvariant.checkIds (Sum.inl gref) |>.run

def RappRef.checkIds (rref : RappRef) : m Unit :=
  CheckIdInvariant.checkIds (Sum.inr rref) |>.run

private def checkUnificationGoalsCore : Sum GoalRef RappRef → MetaM Unit :=
  traverseDown
    (λ gref => do
      let g ← gref.get
      match g.parent? with
      | none => return true
      | some parent => do
        let ugoalOrigins := (← parent.get).unificationGoalOrigins
        for ugoal in g.unificationGoals do
          unless ugoalOrigins.contains ugoal do
            throwError "{Check.tree.name}: in goal {g.id}: unification goal {ugoal.name} is not registered in parent rapp"
        discard $ gref.runMetaMInParentState do
          for ugoal in g.unificationGoals do
            if ← isExprMVarAssigned ugoal then throwError
              "{Check.tree.name}: in goal {g.id}: unification goal {ugoal.name} is already assigned"
        return true)
    (λ rref => do
      let r ← rref.get
      withoutModifyingState do
        restoreState r.metaState
        for (m, _) in r.unificationGoalOrigins do
          let (some _) := (← getMCtx).findDecl? m | throwError
            "{Check.tree.name}: in rapp {r.id}: unification goal {m.name} is not declared in the metavariable context"
          if (← isExprMVarAssigned m) then throwError
            "{Check.tree.name}: in rapp {r.id}: unification goal {m.name} is assigned"
        return true)

def GoalRef.checkUnificationGoals : GoalRef → MetaM Unit :=
  checkUnificationGoalsCore ∘ Sum.inl

def RappRef.checkUnificationGoals : RappRef → MetaM Unit :=
  checkUnificationGoalsCore ∘ Sum.inr

private def checkAcyclicCore (x : Sum GoalRef RappRef) : m Unit := do
  -- We use arrays to store the visited nodes (rather than some data structure
  -- with asymptotically faster lookup) because STRefs only have pointer
  -- equality, not pointer comparison. Besides, this is probably faster anyway
  -- for small to medium trees.
  let visitedGoalRefs : IO.Ref (Array GoalRef) ← ST.mkRef #[]
  let visitedRappRefs : IO.Ref (Array RappRef) ← ST.mkRef #[]
  traverseDown
    (λ gref => do
      if ← (← visitedGoalRefs.get).anyM λ gref' => gref.ptrEq gref' then
        throwError "{Check.tree.name}: search tree contains a cycle."
      visitedGoalRefs.modify λ v => v.push gref
      return true)
    (λ rref => do
      if ← (← visitedRappRefs.get).anyM λ rref' => rref.ptrEq rref' then
        throwError "{Check.tree.name}: search tree contains a cycle."
      visitedRappRefs.modify λ v => v.push rref
      return true)
    x

def GoalRef.checkAcyclic : GoalRef → m Unit :=
  checkAcyclicCore ∘ Sum.inl

def RappRef.checkAcyclic : RappRef → m Unit :=
  checkAcyclicCore ∘ Sum.inr

private def checkConsistentParentChildLinksCore : Sum GoalRef RappRef →
    m Unit :=
  traverseDown
    (λ gref => do
      for c in (← gref.get).children do
        if ← notM $ (← c.get).parent.ptrEq gref then err
      return true)
    (λ rref => do
      for c in (← rref.get).children do
        match (← c.get).parent? with
        | some parent =>
          if ← notM $ parent.ptrEq rref then err
        | none =>
          err
      return true)
  where
    err := throwError "{Check.tree.name}: search tree is not properly linked"

def GoalRef.checkConsistentParentChildLinks : GoalRef → m Unit :=
  checkConsistentParentChildLinksCore ∘ Sum.inl

def RappRef.checkConsistentParentChildLinks : RappRef → m Unit :=
  checkConsistentParentChildLinksCore ∘ Sum.inr

def GoalRef.checkInvariantsIfEnabled (root : GoalRef) : MetaM Unit := do
  let (true) ← Check.tree.isEnabled | return ()
  root.checkConsistentParentChildLinks
  root.checkAcyclic
  root.checkIds
  root.checkUnificationGoals

end Aesop
