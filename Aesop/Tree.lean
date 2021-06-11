/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.MutAltTree
import Aesop.Percent
import Aesop.Rule

open Lean
open Lean.Meta

@[inlineIfReduce]
private def Bool.toYesNo : Bool → Format
  | true => "y"
  | false => "n"

namespace Aesop

/-! ## Node IDs -/

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

instance : ToFormat GoalId where
  format n := format n.toNat

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

instance : ToFormat RappId where
  format n := format n.toNat

end RappId


/-! ## Goal Nodes and Rule Applications -/

structure GoalData : Type where
  id : GoalId
  goal : MVarId
  successProbability : Percent
  normalizationProof : Option Expr
  failedRapps : List RegularRule
  unsafeQueue : Option (List UnsafeRule)
  proven? : Bool
  unprovable? : Bool
  irrelevant? : Bool
  deriving Inhabited

namespace GoalData

def normal? (g : GoalData) : Bool :=
  g.normalizationProof.isSome

structure MessageInfo where
  showGoal : Bool
  showUnsafeQueue : Bool
  showFailedRapps : Bool
  deriving Inhabited

open MessageData in
protected def toMessageData (minfo : MessageInfo) (g : GoalData) : MessageData :=
  let unsafeQueueLength :=
    match g.unsafeQueue with
    | none => f!"<not selected>"
    | some q => format q.length
  m!"Goal {g.id} [{g.successProbability}]" ++ indentDUnlinesSkipEmpty
    [ m!"Unsafe rules in queue: {unsafeQueueLength}, failed: {g.failedRapps.length}",
      join
        [ m!"normal: {g.normal?.toYesNo} | ",
          m!"proven: {g.proven?.toYesNo} | ",
          m!"unprovable: {g.unprovable?.toYesNo} | ",
          m!"irrelevant: {g.irrelevant?.toYesNo}" ],
      toMessageDataIf minfo.showGoal $
        m!"Goal:{indentD g.goal}",
      toMessageDataIf (minfo.showUnsafeQueue && g.unsafeQueue.isSome) $
        m!"Unsafe queue:{indentDUnlines $ g.unsafeQueue.get!.map toMessageData}",
      toMessageDataIf minfo.showFailedRapps $
        m!"Failed rule applications:{indentDUnlines $ g.failedRapps.map toMessageData}" ]

def mkInitial (id : GoalId) (goal : MVarId) (successProbability : Percent) :
    GoalData where
  id := id
  goal := goal
  successProbability := successProbability
  normalizationProof := none
  failedRapps := []
  unsafeQueue := none
  proven? := false
  unprovable? := false
  irrelevant? := false

end GoalData

structure RappData : Type where
  id : RappId
  appliedRule : RegularRule
  successProbability : Percent
  proof : Expr
  proven? : Bool
  unprovable? : Bool
  irrelevant? : Bool
  deriving Inhabited

namespace RappData

structure MessageInfo where
  showProof : Bool

open MessageData in
protected def toMessageData (minfo : MessageInfo) (r : RappData) : MessageData :=
  m!"Rule application {r.id} [{r.successProbability}]" ++ indentDUnlinesSkipEmpty
    [ toMessageData r.appliedRule,
      join
        [ m!"proven: {r.proven?.toYesNo} | ",
          m!"unprovable: {r.unprovable?.toYesNo} | ",
          m!"irrelevant: {r.irrelevant?.toYesNo}" ],
      toMessageDataIf minfo.showProof $
        m!"Proof:{indentD r.proof}" ]

def mkInitial (id : RappId) (appliedRule : RegularRule)
  (successProbability : Percent) (proof : Expr) : RappData where
  id := id
  appliedRule := appliedRule
  successProbability := successProbability
  proof := proof
  proven? := false
  unprovable? := false
  irrelevant? := false

end RappData

abbrev Goal    := MutAltTree IO.RealWorld GoalData RappData
abbrev GoalRef := IO.Ref Goal

abbrev Rapp    := MutAltTree IO.RealWorld RappData GoalData
abbrev RappRef := IO.Ref Rapp

variable {m} [Monad m] [MonadLiftT (ST IO.RealWorld) m]

/-! ## Functions on Goals -/

namespace Goal

/-! ### Constructors -/

@[inline]
def mk (parent : Option RappRef) (rapps : Array RappRef)
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
def normalizationProof (g : Goal) : Option Expr :=
  g.payload.normalizationProof

@[inline]
def failedRapps (g : Goal) : List RegularRule :=
  g.payload.failedRapps

@[inline]
def unsafeQueue (g : Goal) : Option (List UnsafeRule) :=
  g.payload.unsafeQueue

@[inline]
def proven? (g : Goal) : Bool :=
  g.payload.proven?

@[inline]
def unprovable? (g : Goal) : Bool :=
  g.payload.unprovable?

@[inline]
def irrelevant? (g : Goal) : Bool :=
  g.payload.irrelevant?

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
def setNormalizationProof (normalizationProof : Expr) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with normalizationProof := normalizationProof }

@[inline]
def setFailedRapps (failedRapps : List RegularRule) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with failedRapps := failedRapps }

@[inline]
def setUnsafeQueue (unsafeQueue : Option (List UnsafeRule)) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with unsafeQueue := unsafeQueue }

@[inline]
def setProven? (proven? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with proven? := proven? }

@[inline]
def setUnprovable? (unprovable? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with unprovable? := unprovable? }

@[inline]
def setIrrelevant? (irrelevant? : Bool) (g : Goal) : Goal :=
  g.modifyPayload λ d => { d with irrelevant? := irrelevant? }

/-! ### Miscellaneous -/

@[inline]
def normal? (g : Goal) : Bool :=
  g.payload.normal?

def hasNoUnexpandedUnsafeRule (g : Goal) : Bool :=
  match g.unsafeQueue with
  | none => false
  | some q => q.isEmpty

end Goal


/-! ## Functions on Rule Applications -/

namespace Rapp

/-! ### Constructors -/

@[inline]
def mk (parent : Option GoalRef) (subgoals : Array GoalRef)
    (data : RappData) : Rapp :=
  MutAltTree.mk data parent subgoals

/-! ### Getters -/

@[inline]
def subgoals (r : Rapp) : Array GoalRef :=
  r.children

@[inline]
def id (r : Rapp) : RappId :=
  r.payload.id

@[inline]
def appliedRule (r : Rapp) : RegularRule :=
  r.payload.appliedRule

@[inline]
def successProbability (r : Rapp) : Percent :=
  r.payload.successProbability

@[inline]
def proof (r : Rapp) : Expr :=
  r.payload.proof

@[inline]
def proven? (r : Rapp) : Bool :=
  r.payload.proven?

@[inline]
def unprovable? (r : Rapp) : Bool :=
  r.payload.unprovable?

@[inline]
def irrelevant? (r : Rapp) : Bool :=
  r.payload.irrelevant?

-- Setters

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with id := id }

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with appliedRule := appliedRule }

@[inline]
def setSuccessProbability (successProbability : Percent) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with successProbability := successProbability }

@[inline]
def setProof (proof : Expr) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with proof := proof }

@[inline]
def setProven? (proven? : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with proven? := proven? }

@[inline]
def setUnprovable? (unprovable? : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with unprovable? := unprovable? }

@[inline]
def setIrrelevant? (irrelevant? : Bool) (r : Rapp) : Rapp :=
  r.modifyPayload λ r => { r with irrelevant? := irrelevant? }

/-! ### Miscellaneous -/

def subgoalsProven? (r : Rapp) : m Bool :=
  r.subgoals.allM λ subgoal => return (← subgoal.get).proven?

end Rapp

/-! ## Formatting -/

mutual
  private partial def formatTreeGoal (goalMInfo : GoalData.MessageInfo)
      (rappMInfo : RappData.MessageInfo) (goal : Goal) : m MessageData := do
    let goalMsg := goal.payload.toMessageData goalMInfo
    let childrenMsgs ← goal.rapps.mapM λ c => do
      formatTreeRapp goalMInfo rappMInfo (← c.get)
    return goalMsg ++ indentD (MessageData.node childrenMsgs)

  private partial def formatTreeRapp (goalMInfo : GoalData.MessageInfo)
      (rappMInfo : RappData.MessageInfo) (rapp : Rapp) : m MessageData := do
    let rappMsg := rapp.payload.toMessageData rappMInfo
    let childrenMsgs ← rapp.subgoals.mapM λ c => do
      formatTreeGoal goalMInfo rappMInfo (← c.get)
    return rappMsg ++ indentD (MessageData.node childrenMsgs)
end

@[inline]
def Goal.formatTree : GoalData.MessageInfo → RappData.MessageInfo → Goal →
    m MessageData :=
  formatTreeGoal

@[inline]
def Rapp.formatTree : GoalData.MessageInfo → RappData.MessageInfo → Rapp →
    m MessageData :=
  formatTreeRapp

/-! ## Miscellaneous Functions on Goals -/

namespace Goal

def mayHaveUnexpandedRapp (g : Goal) : m Bool := do pure $
  ¬ g.hasNoUnexpandedUnsafeRule ∧
  ¬ (← g.rapps.anyM λ r => return (← r.get : Rapp).appliedRule.isSafe)

def hasProvableRapp (g : Goal) : m Bool :=
  g.rapps.anyM λ r => return ¬ (← r.get).unprovable?

end Goal


/-! ## Proof Extraction -/

namespace GoalRef

/- May only be called *once*. The given goal must be proven. -/
partial def linkProofs (gref : GoalRef) : MetaM Unit := do
  let g ← gref.get
  let (some r) ← g.rapps.findSomeM? λ r => do
    let r ← r.get
    return if r.proven? then some r else none
    | throwError "aesop/linkProofs: internal error: node {g.id} not proven"
  r.subgoals.forM linkProofs
  let goalMVar := g.goal
  checkNotAssigned `aesop goalMVar
  -- TODO check for type-correct assignment?
  -- let goalType ← getMVarType goalMVar
  -- let (true) ← isDefEq goalType r.proof | throwError
  --   "aesop/linkProofs: internal error: proof of rule application {r.id} did not unify with the goal of its parent node {g.id}"
  assignExprMVar g.goal r.proof

/- Only call this after `linkProofs` has been run. -/
def extractProof (gref : GoalRef) : MetaM Expr := do
  let g ← gref.get
  match g.normalizationProof with
  | none => instantiateMVars $ mkMVar g.goal
  | some prf => instantiateMVars prf

end GoalRef

/-! ## Propagating Provability/Unprovability/Irrelevance -/

@[inline]
def Internal.setIrrelevant : Sum GoalRef RappRef → m Unit :=
  MutAltTree.visitDown'
    (λ gref => do
      let g : Goal ← gref.get
      if g.irrelevant?
        then return false -- Subtree should already be marked as irrelevant.
        else do
          gref.set $ g.setIrrelevant? true
          return true)
    (λ rref => do
      let r : Rapp ← rref.get
      if r.irrelevant?
        then return false
        else do
          rref.set $ r.setIrrelevant? true
          return true)

def GoalRef.setIrrelevant : GoalRef → m Unit :=
  Internal.setIrrelevant ∘ Sum.inl

def RappRef.setIrrelevant : RappRef → m Unit :=
  Internal.setIrrelevant ∘ Sum.inr

@[inline]
def Internal.setProven : Sum GoalRef RappRef → m Unit :=
  MutAltTree.visitUp'
    -- Goals are unconditionally marked as proven.
    (λ gref => do
      gref.modify λ (g : Goal) => g.setProven? true
      return true)
    -- Rapps are marked as proven only if they are in fact proven, i.e. if all
    -- their subgoals are (marked as) proven. In this case, we also need to
    -- mark siblings of the rapp (and their descendants) as irrelevant.
    (λ rref => do
      let r : Rapp ← rref.get
      if ¬ (← r.subgoalsProven?)
        then return false
        else do
          rref.set $ r.setProven? true
          let siblings ← MutAltTree.siblings rref
          siblings.forM RappRef.setIrrelevant
          return true)

def GoalRef.setProven : GoalRef → m Unit :=
  Internal.setProven ∘ Sum.inl

def RappRef.setProven : RappRef → m Unit :=
  Internal.setProven ∘ Sum.inr

@[inline]
def Internal.setUnprovable : Sum GoalRef RappRef → m Unit :=
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
          gref.set $ g.setUnprovable? true
          let siblings ← MutAltTree.siblings gref
          siblings.forM GoalRef.setIrrelevant
          return true)
    -- Rapps are unconditionally marked as unprovable.
    (λ rref => do
      rref.modify λ (r : Rapp) => r.setUnprovable? true
      return true)

def GoalRef.setUnprovable : GoalRef → m Unit :=
  Internal.setUnprovable ∘ Sum.inl

def RappRef.setUnprovable : RappRef → m Unit :=
  Internal.setUnprovable ∘ Sum.inr

end Aesop
