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

-- Note: Sets dummy GoalId.
def mkInitial (goal : MVarId) (successProbability : Percent) : GoalData where
  id := GoalId.zero
  goal := goal
  successProbability := successProbability
  normalizationProof := none
  failedRapps := []
  unsafeQueue := none
  proven? := false
  unprovable? := false
  irrelevant? := false

def normal? (g : GoalData) : Bool :=
  g.normalizationProof.isSome

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

def mkInitial (appliedRule : RegularRule) (successProbability : Percent)
  (proof : Expr) : RappData where
  id := RappId.zero
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

/-! ## Miscellaneous Functions on Goals -/

namespace Goal

def mayHaveUnexpandedRapp (g : Goal) : m Bool := do pure $
  ¬ g.hasNoUnexpandedUnsafeRule ∧
  ¬ (← g.rapps.anyM λ r => return (← r.get : Rapp).appliedRule.isSafe)

def hasProvableRapp (g : Goal) : m Bool :=
  g.rapps.anyM λ r => return ¬ (← r.get).unprovable?

end Goal


/-! ## The Search Tree -/

structure Tree where
  root : GoalRef
  nextGoalId : GoalId
  nextRappId : RappId -- TODO make these refs as well?

namespace Tree

def singleton (g : Goal) : m Tree := return {
  root := (← ST.mkRef g)
  nextGoalId := GoalId.one
  nextRappId := RappId.zero }

-- Note: Overwrites the goal ID from g.
def insertGoal (g : GoalData) (parent : RappRef) (t : Tree) :
    m (GoalId × GoalRef × Tree) := do
  let id := t.nextGoalId
  let goalRef ← ST.mkRef $ Goal.mk (some parent) #[] g
  parent.modify λ r => r.addChild goalRef
  return (id, goalRef, { t with nextGoalId := id.succ })

-- Note: Overwrites the rapp ID from r.
def insertRapp (r : RappData) (parent : GoalRef) (t : Tree) :
    m (RappId × RappRef × Tree) := do
  let id := t.nextRappId
  let rappRef ← ST.mkRef $ Rapp.mk (some parent) #[] r
  parent.modify λ g => g.addChild rappRef
  return (id, rappRef, { t with nextRappId := id.succ })

def rootProven? (t : Tree) : m Bool :=
  return (← t.root.get).proven?

def rootUnprovable? (t : Tree) : m Bool :=
  return (← t.root.get).unprovable?

partial def linkProofs (t : Tree) : MetaM Unit :=
  loop t.root
  where
    loop (gref : GoalRef) : MetaM Unit := do
      let g ← gref.get
      let (some r) ← g.rapps.findSomeM? λ r => do
        let r ← r.get
        return if r.proven? then some r else none
        | throwError "aesop/linkProofs: internal error: node {g.id} not proven"
      r.subgoals.forM loop
      let goalMVar := g.goal
      checkNotAssigned `aesop goalMVar
      -- TODO check for type-correct assignment?
      -- let goalType ← getMVarType goalMVar
      -- let (true) ← isDefEq goalType r.proof | throwError
      --   "aesop/linkProofs: internal error: proof of rule application {r.id} did not unify with the goal of its parent node {g.id}"
      assignExprMVar g.goal r.proof

def extractProof (t : Tree) : MetaM Expr := do
  let g ← t.root.get
  match g.normalizationProof with
  | none => instantiateMVars $ mkMVar g.goal
  | some prf => instantiateMVars prf

end Tree

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

-- TODO formatting

end Aesop
