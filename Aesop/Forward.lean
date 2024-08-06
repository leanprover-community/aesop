/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Lean
import Aesop
import Batteries.Lean.HashMap
import Batteries.Data.BinomialHeap.Basic
--
import Aesop.Index.Basic



open Lean Meta
open Batteries (BinomialHeap)

/- Building data stucture for partial matches. -/
/- TODO, figure out how to make sure we don't have duplicate matches.-/

namespace Aesop

def PersistentHashSet.toHashSet [BEq α] [Hashable α]
    (p : PersistentHashSet α) : HashSet α :=
  p.fold (init := ∅) fun result a ↦ result.insert a

def HashSet.inter [BEq α] [Hashable α] (vars1 : HashSet α) (vars2 : HashSet α) :
    HashSet α := Id.run do
  let mut vars : HashSet _ := HashSet.empty
  for el in vars1 do
    match vars2.find? el with
    | none => continue
    | some el => vars := vars.insert el
  return vars

structure Slot where
  /-- Metavariable representing the input hypothesis of the rule -/
  mvarId : MVarId
  /-- Ordering of the slots-/
  slot : Nat
  /-- The metavariables this input hypothesis depends on -/
  deps : HashSet MVarId
  /-- Common variables shared between this slot and the previous slots -/
  common : HashSet MVarId
  /-- Position of the input hypothesis in the rule type -/
  position : Nat
  deriving Inhabited

abbrev Substitution := HashMap MVarId Expr

structure PartialMatch where
  hyps : List FVarId
  subst : Substitution
  level : Nat

instance : BEq PartialMatch where
  beq m₁ m₂ := m₁.hyps == m₂.hyps

/-- TODO: optimise hash in structure-/
instance : Hashable PartialMatch where
  hash m := hash m.hyps

/-- Map:
`(slot, instantiation)` →  a corresponding pair of partial matches and hypotheses -/
structure VariableMap where
  map : PHashMap (Nat × Expr)
    (PersistentHashSet PartialMatch × PersistentHashSet FVarId)
  deriving Inhabited

/-- Collection of variableMaps-/
structure VariableAtlas where
  atlas : PHashMap MVarId VariableMap
  deriving Inhabited

instance VariableAtlas.instEmptyCollection : EmptyCollection VariableAtlas := ⟨⟨.empty⟩⟩


structure RuleState where
  /-- Expression of the associated theorem. -/
  expr : Expr
  /-- Number of input hypotheses of the rule. -/
  len : Nat
  /-- Slots representing each of the maximal input hypotheses. For each index `i` of `slots`,
  `slots[i].slot = i`. -/
  slots : Array Slot
  /-- The conclusion of the rule. (End point of the rule)-/
  conclusion : Expr
  /-- MetaState in which slots and conclusion are valid-/
  metaState : Meta.SavedState
  /-- Atlas associated with the RuleState-/
  atlas : VariableAtlas
  deriving Nonempty /- Can't use Inhabited because metaState isn't-/


def RuleState.ofExpr (thm : Expr) : MetaM RuleState := withoutModifyingState do
  let e ← inferType thm
  let ⟨args, _, conclusion⟩ ← forallMetaTelescope e
  let metaState ← saveState
  let args ← args.mapM fun exp : Expr => do
    let type ← exp.mvarId!.getType
    let deps ← getMVars type
    return (exp.mvarId!, HashSet.ofArray deps)
  let mut slots : Array Slot := Array.mkEmpty args.size
  let mut previousDeps := HashSet.empty
  for h : i in [:args.size] do
    let (mvarId, deps) := args[i]'h.2
    let commonDeps := HashSet.inter previousDeps deps
    -- We will update `slot = 0` with correct position in the final Array later
    slots := slots.push ⟨mvarId, 0, deps, commonDeps, i⟩
    previousDeps := previousDeps.insertMany deps
  let len := slots.size
  slots := slots.filter fun slot => ! previousDeps.contains slot.mvarId
  slots := slots.mapIdx fun slot current => {current with slot}
  let mut atlas : VariableAtlas := ∅
  return {expr := thm, len, slots, metaState, conclusion, atlas}

def RuleState.slot! (r : RuleState) (slot : Nat) : Slot :=
  r.slots[slot]!

/-- `r.slot! slot` contains the information concerning the inputHypothesis. We match this
with a given `hyp`.-/
def RuleState.matchInputHypothesis (r : RuleState) (slot : Nat) (hyp : FVarId) :
    MetaM (Option Substitution) := do
  let slot := r.slot! slot
  r.metaState.runMetaM' do
    let inputHypType ← slot.mvarId.getType
    let hypType ← hyp.getType
    if ← isDefEq inputHypType hypType then
      /- Substitution of metavariables. -/
      /- Note: This was over `slot.common` and not `slot.deps`. We need `slot.deps`
      because, among other issues, `slot.common` is empty in the first slot. Even though
      we don't have dependencies, we still need to keep track of the subs of hyp.
      Otherwise, we would trigger the first panic in `AddHypothesis`.-/
      let mut inst : Substitution := ∅
      for var in slot.deps do
        let assignment ← instantiateMVars (.mvar var)
        if assignment.isMVar then
          throwError "Assigned variable can not be an MVar"
        inst := inst.insert var assignment
      return inst
    else
      return none

/- Use `Lean.Meta.mkAppOptM` to reconstruct conclusion. Need ordering of mVar
(notetoself: these include inputHyps and the variables.)-/
/-- Function reconstructing a rule from a partial match. (We assume `lvl` is the level of `m`.)-/
def RuleState.reconstruct (r : RuleState) (m : PartialMatch) :
    MetaM (Option Expr) := do
  if r.slots.size != m.level then
    panic! "Level of match is not maximal"
  else
    let sortedSlots := r.slots.qsort (fun s₁ s₂ ↦ s₁.position < s₂.position)
    let mut arr := Array.mkArray r.len none
    let mut hyps := m.hyps
    for slot in sortedSlots do
      let hyp := match hyps with
        | [] => panic! "hyps.len = slots.len so we should not run out."
        | x :: _ => x
      hyps := hyps.drop 1
      arr := arr.set! slot.position (some <| .fvar hyp)
    mkAppOptM' r.expr arr

namespace VariableMap

instance : EmptyCollection VariableMap := ⟨⟨.empty⟩⟩

def find? (m : VariableMap) (slot : Nat) (inst : Expr) :
    Option (PersistentHashSet PartialMatch × PersistentHashSet FVarId) :=
  m.map.find? (slot, inst)

def find (m : VariableMap) (slot : Nat) (inst : Expr) :
    PersistentHashSet PartialMatch × PersistentHashSet FVarId :=
  m.find? slot inst |>.getD (∅, ∅)

/-TODO: Here `inst` connect with `MetaM (Option Substitution)`?.-/

/-- The `slot` represents the input hypothesis corresponding to `hyp`-/
def insertHyp (m : VariableMap) (slot : Nat) (inst : Expr) (hyp : FVarId) : VariableMap :=
  match m.find? slot inst with
  | none => {map := m.map.insert (slot, inst) (∅, (∅ : PersistentHashSet _).insert hyp)}
  | some (partialMatches, hyps) =>
    {map := m.map.insert (slot, inst) (partialMatches, hyps.insert hyp)}

/-- The `slot` represents the maximal input hypothesis in `partialMatch`-/
def insertPartialMatches (m : VariableMap) (slot : Nat) (inst : Expr)
    (partialMatch : PartialMatch) : VariableMap :=
  if partialMatch.level == slot then
    match m.find? slot inst with
    | none => {map := m.map.insert (slot, inst) ((∅ : PersistentHashSet _).insert partialMatch, ∅)}
    | some (partialMatches, hyps) =>
      {map := m.map.insert (slot, inst) (partialMatches.insert partialMatch, hyps)}
  else panic! "Level of match is not maximal"

end VariableMap

namespace VariableAtlas

def find (a : VariableAtlas) (var : MVarId) : VariableMap :=
  a.atlas.find? var |>.getD ∅

def modify (a : VariableAtlas) (var : MVarId) (f : VariableMap → VariableMap) : VariableAtlas :=
  match a.atlas.find? var with
  | none => ∅
  | some m => {atlas := a.atlas.insert var (f m)}

/-- Function that adds a hypothesis to the relevent VariableMaps. These are the variables
found in `slot.common` where the input hypothesis associated to `slot` matches `hyp`.
This means that we can unify `slot.MVarId` to `hyp`. -/
def addHypToMaps (a : VariableAtlas) (slot : Slot) (subs : Substitution) (hyp : FVarId) :
    VariableAtlas := Id.run do
  let mut a := a
  for var in slot.common do
    a := a.modify var (·.insertHyp slot.slot (subs.find! var) hyp)
  return a

/-- Function that adds a match to the relevent VariableMaps. If `lvl` is the level of the match,
then `slot.slot = lvl + 1` so the relevent `vars` are the common of the next slot. -/
def addMatchToMaps (a : VariableAtlas) (slot : Slot) (nextSlot : Slot)
    (subs : Substitution) (partialMatch : PartialMatch) : VariableAtlas := Id.run do
  let mut a := a
  for var in nextSlot.common do
    a := a.modify var (fun m => m.insertPartialMatches (slot.slot) (subs.find! var) partialMatch)
  return a

/-- `slot` should not be the first slot. -/
def findPartialMatch (a : VariableAtlas) (slot : Slot) (subst : Substitution) :
    HashSet PartialMatch := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut pms : HashSet PartialMatch :=
      /-TODO: extract-/
      (a.find common[0]).find (slot.slot - 1) (subst.find! common[0])
        |>.1 |> PersistentHashSet.toHashSet
    for var in common[1:] do
      pms := HashSet.inter pms
        <| PersistentHashSet.toHashSet ((a.find var).find (slot.slot - 1) (subst.find! var) |>.1)
    return pms
  else
    panic! "findPartialMatch: common variable array is empty."

/-- Precondition: slot is not the last slot. -/
def findHypotheses (a : VariableAtlas) (slot : Slot) (subst : Substitution) : HashSet FVarId :=
  Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps : HashSet FVarId :=
      /-TODO: extract-/
      (a.find common[0]).find (slot.slot + 1) (subst.find! common[0])
        |>.2 |> PersistentHashSet.toHashSet
    for var in common[1:] do
      hyps := HashSet.inter hyps
        <| PersistentHashSet.toHashSet ((a.find var).find (slot.slot + 1) (subst.find! var) |>.2)
    return hyps
  else
    panic! "findHypotheses: common variable array is empty."

end VariableAtlas

namespace RuleState


/-- Precondition: The `slot` represents the maximal input hypothesis in `partialMatch`.
This means that `m.level = slot.slot`.
-/
partial def AddMatch (r : RuleState) (slot : Slot) (m : PartialMatch) :
    MetaM (RuleState × Array Expr) := do
  let subst := m.subst
  let mut r := r
  let mut fullMatches : Array Expr := ∅
  if r.slots.size == slot.slot then
    match ← r.reconstruct m with
    | none => panic! "Reconstruct failed to provide an expression"
    | some expr => return ⟨r, #[expr]⟩
  else
    let atlas := r.atlas.addMatchToMaps slot (r.slot! (slot.slot + 1)) subst m
    r := { r with atlas }
    for hyp in r.atlas.findHypotheses slot subst do
      let x ← r.AddMatch slot ⟨hyp :: m.hyps, subst, slot.slot + 1⟩
      r := x.1
      fullMatches := fullMatches.append x.2
    return ⟨r, fullMatches⟩

/-- Precondition: The `slot` represents the input hypothesis corresponding to `hyp` -/
def AddHypothesis (r : RuleState) (slot : Slot) (h : FVarId) :
    MetaM (RuleState × Array Expr) := do
  match ← r.matchInputHypothesis slot.slot h with
  | none => panic! "The rule should have a non-trivial substitution at every slot."
  | some subst =>
    let mut r := r
    let atlas := r.atlas.addHypToMaps slot subst h
    let mut fullMatches : Array Expr := ∅
    r := { r with atlas }
    if slot.slot == 0 then
      return ← r.AddMatch slot ⟨[h], subst, 0⟩
    else
      for pm in r.atlas.findPartialMatch slot subst do
        /- TODO: Add a check that we are not overwriting substitutions?
        Indeed, the when we have the same key, we should have same value. (TestMaybe)-/
        let mut currInst : Substitution :=
          Lean.HashMap.mergeWith (fun _ _ v₂ ↦ v₂) subst pm.subst
        /- Note Prob faster to do this ourselves with fold:
            let mut currInst' : Substitution :=
            subst.fold (fun (s : Substitution) k v => s.insert k v) pm.subst -/
        /- We add `hyp` at the beginning, update relevant insts and the level. -/
        let x ← r.AddMatch slot ⟨h :: pm.hyps, currInst, slot.slot⟩
        r := x.1
        fullMatches := fullMatches.append x.2
      return ⟨r, fullMatches⟩

end RuleState

open Lean Lean.Meta

inductive Prio : Type where
  | normsafe (n : Int) : Prio
  | «unsafe» (p : Percent) : Prio

structure ForwardRule where
  name : RuleName
  expr : Expr
  prio : Prio

instance : BEq ForwardRule :=
  ⟨λ r₁ r₂ => r₁.name == r₂.name⟩

instance : Hashable ForwardRule :=
  ⟨λ r => hash r.name⟩

instance : Ord ForwardRule :=
  ⟨λ r₁ r₂ => compare r₁.name r₂.name⟩

/--
Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`, `i : Nat`
and the `i`-th argument of the type of `r.expr` (counting from zero) likely
unifies with `T`.
-/
structure ForwardIndex where
  tree : DiscrTree (ForwardRule × Slot)

namespace ForwardIndex

def insert (r : ForwardRule) (idx : ForwardIndex) : MetaM ForwardIndex := do
  let type ← inferType r.expr
  withReducible do
    forallTelescopeReducing type λ args _ => do
      let args' ← args.mapM fun exp : Expr => do
        let type ← exp.mvarId!.getType
        let deps ← getMVars type
        return (exp.mvarId!, HashSet.ofArray deps)
      let mut tree := idx.tree
      for h : i in [:args.size] do
        let arg := args[i]!
        tree ← sorry -- tree.insert arg (r, i) discrTreeConfig
      return ⟨tree⟩

def get (idx : ForwardIndex) (e : Expr) : MetaM (Array (ForwardRule × Slot)) :=
  idx.tree.getUnify e discrTreeConfig

end ForwardIndex

section ForwardState

structure QueueEntry where
  expr : Expr
  prio : Prio

/- Int with higher number is worse-/
/- Percentage with higher number is better-/
def QueueEntry.le
    (q₁ q₂ : QueueEntry) : Bool := match q₁.prio with
    | Prio.normsafe n =>
      match q₂.prio with
        | Prio.normsafe m => n ≤ m
        | Prio.«unsafe» _ => sorry -- Should not happen as Queues are separated.
    | Prio.«unsafe» p =>
      match q₂.prio with
        | Prio.normsafe m => sorry
        | Prio.«unsafe» q => p ≥ q

structure ForwardState where
  /- Missing associated goal? -/
  /-- Map from the rule's `RuleName` to it's `RuleState`-/
  ruleStates : HashMap RuleName RuleState
  /-- The index of Forward Rule to be unified against. -/
  index : ForwardIndex
  /- Arrays of complete matches.-/
  normQueue : (BinomialHeap (QueueEntry) (QueueEntry.le))
  safeQueue : (BinomialHeap (QueueEntry) (QueueEntry.le))
  unsafeQueue : (BinomialHeap (QueueEntry) (QueueEntry.le))


/- Index can also give the `Expr` of which rule it thinks we should look at
and the slot `i` associated to the hypothesis.-/
def ForwardState.AddHypothesis (h : FVarId) (forwardState : ForwardState) : MetaM ForwardState := do
  let mut forwardState := forwardState
  for (r, s) in ← forwardState.index.get (← h.getType) do
    let RS ← match forwardState.ruleStates.find? r.name with
      | some n => pure n
      | none => RuleState.ofExpr r.expr
    let (RS, Arr) ← RS.AddHypothesis s h
    forwardState := {
      forwardState with
      ruleStates := forwardState.ruleStates.insert r.name RS
    }
    match r.name.phase with
    | PhaseName.norm =>
      for expr in Arr do
        forwardState := {
          forwardState with
          normQueue := forwardState.normQueue.insert {expr, prio := r.prio}
        }
    | PhaseName.safe =>
      for expr in Arr do
        forwardState := {
          forwardState with
          safeQueue := forwardState.safeQueue.insert {expr, prio := r.prio}
        }
    | PhaseName.«unsafe» =>
      for expr in Arr do
        forwardState := {
          forwardState with
          unsafeQueue := forwardState.unsafeQueue.insert {expr, prio := r.prio}
        }
  /- Return updated map-/
  return forwardState

-- Are we removing the hyps associated with h?
def ForwardState.RemoveHypothesis (h : FVarId) (forwardState : ForwardState) :
    MetaM ForwardState := do sorry

/-- Returns the queue of safe rules. -/
def ForwardState.GetNormRules (forwardState : ForwardState) :
    (BinomialHeap (QueueEntry) (QueueEntry.le)) := forwardState.normQueue

/-- Returns the queue of safe rules. -/
def ForwardState.GetSafeRules (forwardState : ForwardState) :
    (BinomialHeap (QueueEntry) (QueueEntry.le)) := forwardState.safeQueue

/-- Returns the queue of safe rules. -/
def ForwardState.GetUnsafeRules (forwardState : ForwardState) :
    (BinomialHeap (QueueEntry) (QueueEntry.le)) := forwardState.unsafeQueue

/-- Returns the queue of safe rules. -/
def ForwardState.PopNormRules (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.normQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)

/-- Returns the queue of safe rules. -/
def ForwardState.PopSafeRules (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.safeQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)

/-- Returns the queue of safe rules. -/
def ForwardState.PopUnsafeRules (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.unsafeQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)


end ForwardState




end Aesop
