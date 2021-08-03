/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Check
import Aesop.MutAltTree
import Aesop.Rule
import Aesop.Util
import Aesop.Tracing
import Std

open Lean
open Lean.Meta
open Std

variable [Monad m] [MonadOptions m] [MonadLiftT (ST IO.RealWorld) m]
  [MonadError m]

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


/-! ## Goal Nodes and Rule Applications -/

inductive ProofStatus
  | unproven
  | provenByRuleApplication
  | provenByNormalization
  deriving Inhabited, BEq

namespace ProofStatus

def isProven : ProofStatus → Bool
  | unproven => false
  | provenByRuleApplication => true
  | provenByNormalization => true

end ProofStatus


-- Invariant: if proofStatus = provenByNormalization then isNormal = true
-- Invariant: All goal IDs in a tree are distinct.
-- Invariant: The goal ID of a node is smaller than the goal IDs of its
--   descendant goals.
structure GoalData : Type where
  id : GoalId
  goal : MVarId
  successProbability : Percent
  failedRapps : List RegularRule
  unsafeQueue : Option (List UnsafeRule)
  proofStatus : ProofStatus
  isUnprovable : Bool
  isIrrelevant : Bool
  isNormal : Bool
  deriving Inhabited

namespace GoalData

def isProven (g : GoalData) : Bool :=
  g.proofStatus.isProven

structure MessageInfo where
  showGoal : Bool
  showUnsafeQueue : Bool
  showFailedRapps : Bool
  deriving Inhabited

protected def getMessageInfo (traceCtx : TraceContext) : m MessageInfo := do
  return {
    showGoal := (← TraceOption.showGoals.get traceCtx)
    showUnsafeQueue := (← TraceOption.showUnsafeQueues.get traceCtx)
    showFailedRapps := (← TraceOption.showFailedRapps.get traceCtx)
  }

open MessageData in
protected def toMessageData (traceCtx : TraceContext) (g : GoalData) :
    m MessageData := do
  let minfo ← GoalData.getMessageInfo traceCtx
  let unsafeQueueLength :=
    match g.unsafeQueue with
    | none => f!"<not selected>"
    | some q => format q.length
  return m!"Goal {g.id} [{g.successProbability.toHumanString}]" ++ nodeFiltering #[
    m!"Unsafe rules in queue: {unsafeQueueLength}, failed: {g.failedRapps.length}",
    join
      [ m!"normal: {g.isNormal.toYesNo} | ",
        m!"proven: {g.isProven.toYesNo} | ",
        m!"unprovable: {g.isUnprovable.toYesNo} | ",
        m!"irrelevant: {g.isIrrelevant.toYesNo}" ],
    if ¬ minfo.showGoal then none else
      m!"Goal:{indentD $ ofGoal g.goal}",
    if ¬ minfo.showUnsafeQueue || g.unsafeQueue.isNone then none else
      m!"Unsafe queue:{indentDUnlines $ g.unsafeQueue.get!.map toMessageData}",
    if ¬ minfo.showFailedRapps then none else
      m!"Failed rule applications:{indentDUnlines $ g.failedRapps.map toMessageData}" ]

protected def mkInitial (id : GoalId) (goal : MVarId)
    (successProbability : Percent) : GoalData where
  id := id
  goal := goal
  successProbability := successProbability
  failedRapps := []
  unsafeQueue := none
  proofStatus := ProofStatus.unproven
  isUnprovable := false
  isIrrelevant := false
  isNormal := false

end GoalData

-- This is necessary to work around a compiler bug. If we inline this
-- definition, the nested inductive compiler fails on `RappDataUnsafe`.
private abbrev UnificationGoalOriginsMap α := PersistentHashMap MVarId α

-- Invariant: All rapp IDs in a tree are distinct.
-- Invariant: The rapp ID of a node is smaller than the rapp IDs of its
--   descendant rapps.
-- Invariant: The mvars in `unificationGoalOrigins` are declared but unassigned
--   in `state`.
-- Invariant: The rapps referenced by `unificationGoalOrigins` are ancestors of
--   this rapp.
structure RappData' (α : Type) : Type where
  id : RappId
  state : Meta.SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  unificationGoalOrigins : UnificationGoalOriginsMap α
  appliedRule : RegularRule
  successProbability : Percent
  isProven : Bool
  isUnprovable : Bool
  isIrrelevant : Bool
  deriving Inhabited

unsafe inductive RappDataUnsafe
  | mk :
    RappData' (IO.Ref (MutAltTree IO.RealWorld RappDataUnsafe GoalData)) →
    RappDataUnsafe

structure RappDataSpec where
  RappData : Type
  intro :
    RappData' (IO.Ref (MutAltTree IO.RealWorld RappData GoalData)) →
    RappData
  elim :
    RappData →
    RappData' (IO.Ref (MutAltTree IO.RealWorld RappData GoalData))

unsafe def rappDataImplUnsafe : RappDataSpec where
  RappData := RappDataUnsafe
  intro := RappDataUnsafe.mk
  elim | RappDataUnsafe.mk x => x

@[implementedBy rappDataImplUnsafe]
constant rappDataImpl : RappDataSpec := {
  RappData := Unit
  intro := λ _ => arbitrary
  elim := λ _ => arbitrary
}

def RappData := rappDataImpl.RappData

abbrev Goal    := MutAltTree IO.RealWorld GoalData RappData
abbrev GoalRef := IO.Ref Goal

abbrev Rapp    := MutAltTree IO.RealWorld RappData GoalData
abbrev RappRef := IO.Ref Rapp

namespace RappData

@[inline]
def mk : RappData' RappRef → RappData :=
  rappDataImpl.intro

@[inline]
def elim : RappData → RappData' RappRef :=
  rappDataImpl.elim

@[inline]
def modify (f : RappData' RappRef → RappData' RappRef) (r : RappData) :
    RappData :=
  mk $ f $ elim r

instance : Inhabited RappData where
  default := mk arbitrary

@[inline]
def id (r : RappData) : RappId :=
  r.elim.id

@[inline]
def state (r : RappData) : Meta.SavedState :=
  r.elim.state

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
def isProven (r : RappData) : Bool :=
  r.elim.isProven

@[inline]
def isUnprovable (r : RappData) : Bool :=
  r.elim.isUnprovable

@[inline]
def isIrrelevant (r : RappData) : Bool :=
  r.elim.isIrrelevant

@[inline]
def setId (id : RappId) (r : RappData) : RappData :=
  r.modify λ r => { r with id := id }

@[inline]
def setState (state : Meta.SavedState) (r : RappData) : RappData :=
  r.modify λ r => { r with state := state }

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
def setProven (isProven : Bool) (r : RappData) : RappData :=
  r.modify λ r => { r with isProven := isProven }

@[inline]
def setUnprovable (isUnprovable : Bool) (r : RappData) : RappData :=
  r.modify λ r => { r with isUnprovable := isUnprovable }

@[inline]
def setIrrelevant (isIrrelevant : Bool) (r : RappData) : RappData :=
  r.modify λ r => { r with isIrrelevant := isIrrelevant }

open MessageData in
protected def toMessageData (traceCtx : TraceContext) (r : RappData) :
    m MessageData := do
  let showUnificationGoalOrigins ← TraceOption.showUnificationGoals.get traceCtx
  let unificationGoalOrigins : Option MessageData ←
    if ¬ showUnificationGoalOrigins || r.unificationGoalOrigins.isEmpty
      then pure none
      else do
        let origins ← r.unificationGoalOrigins.toList.mapM $ λ (mvarId, rref) =>
          return (mkMVar mvarId, (← rref.get).payload.id)
        pure $ some $ m!"unification goals:" ++ node #[toMessageData origins]
  return m!"Rapp {r.id} [{r.successProbability.toHumanString}]" ++
    nodeFiltering #[
      toMessageData r.appliedRule,
      join
        [ m!"proven: {r.isProven.toYesNo} | ",
          m!"unprovable: {r.isUnprovable.toYesNo} | ",
          m!"irrelevant: {r.isIrrelevant.toYesNo}" ],
      unificationGoalOrigins ]

protected def mkInitial (id : RappId) (state : Meta.SavedState)
    (unificationGoalOrigins : PersistentHashMap MVarId RappRef)
    (appliedRule : RegularRule) (successProbability : Percent) : RappData := mk
  { id := id
    state := state
    unificationGoalOrigins := unificationGoalOrigins
    appliedRule := appliedRule
    successProbability := successProbability
    isProven := false
    isUnprovable := false
    isIrrelevant := false }

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
def failedRapps (g : Goal) : List RegularRule :=
  g.payload.failedRapps

@[inline]
def unsafeQueue (g : Goal) : Option (List UnsafeRule) :=
  g.payload.unsafeQueue

@[inline]
def proofStatus (g : Goal) : ProofStatus :=
  g.payload.proofStatus

@[inline]
def isProven (g : Goal) : Bool :=
  g.payload.isProven

@[inline]
def isUnprovable (g : Goal) : Bool :=
  g.payload.isUnprovable

@[inline]
def isIrrelevant (g : Goal) : Bool :=
  g.payload.isIrrelevant

@[inline]
def isNormal (g : Goal) : Bool :=
  g.payload.isNormal

/-! ### Setters -/

@[inline]
def setId (id : GoalId) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with id := id }

@[inline]
def setGoal (goal : MVarId) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with goal := goal }

@[inline]
def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with successProbability := successProbability }

@[inline]
def setFailedRapps (failedRapps : List RegularRule) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with failedRapps := failedRapps }

@[inline]
def setUnsafeQueue (unsafeQueue : Option (List UnsafeRule)) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with unsafeQueue := unsafeQueue }

@[inline]
def setProofStatus (proven? : ProofStatus) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with proofStatus := proven? }

@[inline]
def setUnprovable (unprovable? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with isUnprovable := unprovable? }

@[inline]
def setIrrelevant (irrelevant? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with isIrrelevant := irrelevant? }

@[inline]
def setNormal (normal? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with isNormal := normal? }

/-! ### Miscellaneous -/

def hasNoUnexpandedUnsafeRule (g : Goal) : Bool :=
  match g.unsafeQueue with
  | none => false
  | some q => q.isEmpty

def isActive (g : Goal) : Bool :=
  ! (g.isProven || g.isUnprovable || g.isIrrelevant)

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
def state (r : Rapp) : Meta.SavedState :=
  r.payload.state

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
def isProven (r : Rapp) : Bool :=
  r.payload.isProven

@[inline]
def isUnprovable (r : Rapp) : Bool :=
  r.payload.isUnprovable

@[inline]
def isIrrelevant (r : Rapp) : Bool :=
  r.payload.isIrrelevant

-- Setters

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setId id

@[inline]
def setState (state : Meta.SavedState) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setState state

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
def setProven (isProven : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setProven isProven

@[inline]
def setUnprovable (isUnprovable : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setUnprovable isUnprovable

@[inline]
def setIrrelevant (isIrrelevant : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => r.setIrrelevant isIrrelevant

/-! ### Miscellaneous -/

def allSubgoalsProven (r : Rapp) : m Bool :=
  r.subgoals.allM λ subgoal => return (← subgoal.get).isProven

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
  runMetaMInSavedState r.state x

@[inline]
def Rapp.runMetaMModifying (x : MetaM α) (r : Rapp) : MetaM (α × Rapp) := do
  let (result, finalState) ← r.runMetaM x
  return (result, r |>.setState finalState)

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

def Goal.toMessageData (traceCtx : TraceContext) (g : Goal) :
    MetaM MessageData :=
  match g.parent with
  | none => g.payload.toMessageData traceCtx
  | some (rref : RappRef) => do
    let (res, _) ← rref.runMetaM do
      addMessageContext (← g.payload.toMessageData traceCtx)
    return res

def GoalRef.toMessageData (traceCtx : TraceContext) (gref : GoalRef) :
    MetaM MessageData := do
  (← gref.get).toMessageData traceCtx

def Rapp.toMessageData (traceCtx : TraceContext) (r : Rapp) :
    MetaM MessageData := do
  let (res, _) ← r.runMetaM do
    addMessageContext (← r.payload.toMessageData traceCtx)
  return res

def RappRef.toMessageData (traceCtx : TraceContext) (rref : RappRef) :
    MetaM MessageData := do
  (← rref.get).toMessageData traceCtx

def nodeMessageSeparator : MessageData :=
  m!"-*-*-*-*-*-\n"

mutual
  private partial def goalTreeToMessageData (traceCtx : TraceContext) (goal : Goal) :
      MetaM MessageData := do
    let goalMsg ← goal.toMessageData traceCtx
    let childrenMsgs ← goal.rapps.mapM λ c => do
      rappTreeToMessageData traceCtx (← c.get)
    return nodeMessageSeparator ++ goalMsg ++ MessageData.node childrenMsgs

  private partial def rappTreeToMessageData (traceCtx : TraceContext) (rapp : Rapp) :
      MetaM MessageData := do
    let rappMsg ← rapp.toMessageData traceCtx
    let childrenMsgs ← rapp.subgoals.mapM λ c => do
      goalTreeToMessageData traceCtx (← c.get)
    return nodeMessageSeparator ++ rappMsg ++ MessageData.node childrenMsgs
end

def Goal.treeToMessageData (traceCtx : TraceContext) (g : Goal) :
    MetaM MessageData :=
  goalTreeToMessageData traceCtx g

def GoalRef.treeToMessageData (traceCtx : TraceContext) (gref : GoalRef) :
    MetaM MessageData := do
  (← gref.get).treeToMessageData traceCtx

def Rapp.treeToMessageData (traceCtx : TraceContext) (r : Rapp) :
    MetaM MessageData := do
  rappTreeToMessageData traceCtx r

def RappRef.treeToMessageData (traceCtx : TraceContext) (rref : RappRef) :
    MetaM MessageData := do
  (← rref.get).treeToMessageData traceCtx


/-! ## Miscellaneous Functions on Goals -/

namespace Goal

def mayHaveUnexpandedRapp (g : Goal) : m Bool := do pure $
  ¬ g.hasNoUnexpandedUnsafeRule ∧
  ¬ (← g.rapps.anyM λ r => return (← r.get : Rapp).appliedRule.isSafe)

def hasProvableRapp (g : Goal) : m Bool :=
  g.rapps.anyM λ r => return ¬ (← r.get).isUnprovable

def firstProvenRapp? (g : Goal) : m (Option RappRef) :=
  g.rapps.findSomeM? λ rref =>
    return if (← rref.get).isProven then some rref else none

def unificationGoalOrigins (g : Goal) : m (PersistentHashMap MVarId RappRef) :=
  match g.parent with
  | some rref => return Rapp.unificationGoalOrigins (← rref.get)
  | none => return PersistentHashMap.empty

end Goal

def GoalRef.unificationGoalOrigins (gref : GoalRef) :
    m (PersistentHashMap MVarId RappRef) := do
  (← gref.get).unificationGoalOrigins


/-! ## Propagating Provability/Unprovability/Irrelevance -/

@[inline]
def setIrrelevantImpl : Sum GoalRef RappRef → m Unit :=
  MutAltTree.visitDown'
    (λ gref => do
      let g : Goal ← gref.get
      if g.isIrrelevant
        then return false -- Subtree should already be marked as irrelevant.
        else do
          gref.set $ g.setIrrelevant true
          return true)
    (λ rref => do
      let r : Rapp ← rref.get
      if r.isIrrelevant
        then return false
        else do
          rref.set $ r.setIrrelevant true
          return true)

def GoalRef.setIrrelevant : GoalRef → m Unit :=
  setIrrelevantImpl ∘ Sum.inl

def RappRef.setIrrelevant : RappRef → m Unit :=
  setIrrelevantImpl ∘ Sum.inr

@[inline]
private def setProvenImpl : Sum GoalRef RappRef → m Unit :=
  MutAltTree.visitUp'
    -- Goals are unconditionally marked as proven.
    (λ gref => do
      gref.modify λ (g : Goal) =>
        g.setProofStatus ProofStatus.provenByRuleApplication
      return true)
    -- Rapps are marked as proven only if they are in fact proven, i.e. if all
    -- their subgoals are (marked as) proven. In this case, we also need to
    -- mark siblings of the rapp (and their descendants) as irrelevant.
    (λ rref => do
      let r : Rapp ← rref.get
      if ¬ (← r.allSubgoalsProven)
        then return false
        else do
          rref.set $ r.setProven true
          let siblings ← MutAltTree.siblings rref
          siblings.forM RappRef.setIrrelevant
          return true)

def GoalRef.setProven : GoalRef → m Unit :=
  setProvenImpl ∘ Sum.inl

def RappRef.setProven : RappRef → m Unit :=
  setProvenImpl ∘ Sum.inr

@[inline]
private def setUnprovableImpl : Sum GoalRef RappRef → m Unit :=
  MutAltTree.visitUp'
    -- Goals are marked as unprovable only if they are in fact unprovable, i.e.
    -- if all their rule applications are unprovable and they do not have
    -- unexpanded rule applications. In this case, we also need to mark
    -- siblings of the goal (and their descendants) as irrelevant.
    (λ gref => do
      let g : Goal ← gref.get
      if (← g.mayHaveUnexpandedRapp <||> g.hasProvableRapp)
        then return false
        else do
          gref.set $ g.setUnprovable true
          let siblings ← MutAltTree.siblings gref
          siblings.forM GoalRef.setIrrelevant
          return true)
    -- Rapps are unconditionally marked as unprovable.
    (λ rref => do
      rref.modify λ (r : Rapp) => r.setUnprovable true
      return true)

def GoalRef.setUnprovable : GoalRef → m Unit :=
  setUnprovableImpl ∘ Sum.inl

def RappRef.setUnprovable : RappRef → m Unit :=
  setUnprovableImpl ∘ Sum.inr


/-! ## Copying Trees -/

namespace TreeCopy

structure State where
  nextGoalId : GoalId
  nextRappId : RappId
  goalMap : HashMap GoalId GoalRef
  rappMap : HashMap RappId RappRef

abbrev TreeCopyT := StateRefT' IO.RealWorld State

namespace TreeCopyT

def run (s : State) (x : TreeCopyT m α) : m (α × State) :=
  StateRefT'.run x s

def run' (nextGoalId : GoalId) (nextRappId : RappId) (x : TreeCopyT m α) :
    m (α × State) :=
  x.run
    { nextGoalId := nextGoalId,
      nextRappId := nextRappId,
      goalMap := HashMap.empty,
      rappMap := HashMap.empty }

instance [AddErrorMessageContext m] : AddErrorMessageContext (TreeCopyT m) where
  add := λ stx msg => StateRefT'.lift $ AddErrorMessageContext.add stx msg

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
      Goal.mk (some parent) #[] { g.payload with id := newGoalId }
    modify λ s => { s with goalMap := s.goalMap.insert g.id newGoalRef }
    parent.modify λ r => r.addChild newGoalRef
    g.rapps.forM λ rref => discard $ copyRappTree newGoalRef rref
    return newGoalRef

  -- Copies `rref` and all its descendants. The copy of `rref` becomes a child
  -- of `parent`. Returns the copy of `gref`.
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
    r.subgoals.forM λ gref => discard $ copyGoalTree newRappRef gref
    return newRappRef
end

end TreeCopy

def GoalRef.copyTree (nextGoalId : GoalId) (nextRappId : RappId)
  (parent : RappRef) (gref : GoalRef) : m (GoalRef × TreeCopy.State) := do
  TreeCopy.copyGoalTree parent gref |>.run' nextGoalId nextRappId

def RappRef.copyTree (nextGoalId : GoalId) (nextRappId : RappId)
  (parent : GoalRef) (rref : RappRef) : m (RappRef × TreeCopy.State) := do
  TreeCopy.copyRappTree parent rref |>.run' nextGoalId nextRappId


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

-- TODO check whether the unification goal origins are correct
mutual
  private partial def checkUnificationGoalOriginsGoal (gref : GoalRef) :
      MetaM Unit := do
    (← gref.get).rapps.forM checkUnificationGoalOriginsRapp

  private partial def checkUnificationGoalOriginsRapp (rref : RappRef) :
      MetaM Unit := do
    let r ← rref.get
    withoutModifyingState do
      restoreState r.state
      for (m, _) in r.unificationGoalOrigins do
        let (some _) ← (← getMCtx).findDecl? m | throwError
          "{Check.tree.name}: in rapp {r.id}: unification goal {m} is not declared in the metavariable context"
        if (← isExprMVarAssigned m) then throwError
          "{Check.tree.name}: in rapp {r.id}: unification goal {m} is assigned"
    r.subgoals.forM checkUnificationGoalOriginsGoal

end

def GoalRef.checkUnificationGoalOrigins : GoalRef → MetaM Unit :=
  checkUnificationGoalOriginsGoal

def RappRef.checkUnificationGoalOrigins : RappRef → MetaM Unit :=
  checkUnificationGoalOriginsRapp

def GoalRef.checkInvariantsIfEnabled (root : GoalRef) : MetaM Unit := do
  let (true) ← Check.tree.isEnabled | return ()
  unless (← MutAltTree.hasConsistentParentChildLinks root) do
    throwError "{Check.tree.name}: search tree is not properly linked"
  unless (← MutAltTree.isAcyclic root) do
    throwError "{Check.tree.name}: search tree contains a cycle"
  root.checkIds
  root.checkUnificationGoalOrigins

end Aesop
