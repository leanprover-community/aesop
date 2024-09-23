/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Percent
import Batteries.Data.BinomialHeap.Basic
import Batteries.Lean.HashMap
import Batteries.Lean.HashSet
import Batteries.Lean.Meta.SavedState

open Lean Lean.Meta
open Batteries (BinomialHeap)

/- Building data stucture for partial matches. -/
/- TODO, figure out how to make sure we don't have duplicate matches.-/

namespace Aesop

-- TODO move to Util
def PHashSet.toHashSet [BEq α] [Hashable α] (p : PHashSet α) : HashSet α :=
  p.fold (init := ∅) fun result a ↦ result.insert a

-- TODO move to Util
def HashSet.inter [BEq α] [Hashable α] (s₁ : HashSet α) (s₂ : HashSet α) :
    HashSet α :=
  let (s₁, s₂) := if s₁.size < s₂.size then (s₁, s₂) else (s₂, s₁)
  s₁.fold (init := ∅) λ result k =>
    if s₂.contains k then result.insert k else result

structure Slot where
  /-- Metavariable representing the input hypothesis of this slot. -/
  mvarId : MVarId
  /-- Index of the slot. Slots are always part of a list of slots, and `index`
  is the 0-based index of this slot in that list. -/
  index : Nat
  /-- The previous input hypotheses that the input hypothesis of this slot depends on. -/
  deps : HashSet MVarId
  /-- Common variables shared between this slot and the previous slots. -/
  common : HashSet MVarId
  /-- Position of the input hypothesis represented by this slot in the rule type. -/
  hypIndex : Nat
  deriving Inhabited

abbrev Substitution := AssocList MVarId Expr

structure PartialMatch where
  hyps : List FVarId
  subst : Substitution
  level : Nat
  deriving Inhabited

instance : BEq PartialMatch where
  beq m₁ m₂ := m₁.hyps == m₂.hyps

instance : Hashable PartialMatch where
  hash m := hash m.hyps

/-- Partial matches associated with a particular slot instantiation. An entry
`s ↦ i ↦ (ms, hs)` indicates that for the instantiation `i` of slot `s`, we have
partial matches `ms` containing hypotheses `hs`. -/
structure InstMap where
  map :
    PHashMap Nat
      (PHashMap Expr (PHashSet PartialMatch × PHashSet FVarId))
  deriving Inhabited

instance : EmptyCollection InstMap :=
  ⟨⟨.empty⟩⟩

/-- Map from variables to the partial matches of slots whose types contain the
variables. -/
structure VariableMap where
  map : PHashMap MVarId InstMap
  deriving Inhabited

instance : EmptyCollection VariableMap :=
  ⟨⟨.empty⟩⟩

structure RuleState where
  /-- Expression of the associated theorem. -/
  expr : Expr
  /-- Number of input hypotheses of the rule. -/
  len : Nat
  /-- Slots representing each of the maximal input hypotheses. For each index
  `i` of `slots`, `slots[i].index = i`. -/
  slots : Array Slot
  /-- The conclusion of the rule. -/
  conclusion : Expr
  /-- MetaState in which slots and conclusion are valid-/
  metaState : Meta.SavedState
  /-- Variable map. -/
  variableMap : VariableMap
  deriving Nonempty


def RuleState.ofExpr (thm : Expr) : MetaM RuleState := withoutModifyingState do
  let e ← inferType thm
  let ⟨args, _, conclusion⟩ ← forallMetaTelescope e
  let metaState ← saveState
  let args ← args.mapM fun expr : Expr => do
    let type ← expr.mvarId!.getType -- X: What does this do?
    let deps ← getMVars type
    return (expr.mvarId!, HashSet.ofArray deps)
  let mut slots : Array Slot := Array.mkEmpty args.size
  let mut previousDeps := HashSet.empty
  for h : i in [:args.size] do
    let (mvarId, deps) := args[i]'h.2
    let commonDeps := HashSet.inter previousDeps deps
    /- We update `slot = 0` with correct ordering later (see **) -/
    slots := slots.push ⟨mvarId, 0, deps, commonDeps, i⟩
    previousDeps := previousDeps.insertMany deps
  let len := slots.size
  /- Filtering out non-input hypetheses-/
  slots := slots.filter fun slot => ! previousDeps.contains slot.mvarId
  /- (**) Assigns ordering of slots -/
  slots := slots.mapIdx fun index current => {current with index}
  return {expr := thm, variableMap := ∅, len, slots, metaState, conclusion }

def RuleState.slot! (r : RuleState) (slot : Nat) : Slot :=
  r.slots[slot]!

/-- `r.slot! slot` contains the information concerning the inputHypothesis. We match this
with a given `hyp`.-/
def RuleState.matchInputHypothesis? (r : RuleState) (slot : Nat) (hyp : FVarId) :
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
    let sortedSlots := r.slots.qsort (fun s₁ s₂ ↦ s₁.hypIndex < s₂.hypIndex)
    let mut arr := Array.mkArray r.len none
    let mut hyps := m.hyps
    for slot in sortedSlots do
      let hyp := match hyps with
        | [] => panic! "hyps.len = slots.len so we should not run out."
        | x :: _ => x
      hyps := hyps.drop 1
      arr := arr.set! slot.hypIndex (some <| .fvar hyp)
    mkAppOptM' r.expr arr

namespace InstMap

instance : EmptyCollection InstMap := ⟨⟨.empty⟩⟩

def find? (m : InstMap) (slot : Nat) (inst : Expr) :
    Option (PHashSet PartialMatch × PHashSet FVarId) :=
  match (m.map.find? slot) with
  | none => none
  | some map => map.find? inst

def findD (m : InstMap) (slot : Nat) (inst : Expr) :
    PHashSet PartialMatch × PHashSet FVarId :=
  m.find? slot inst |>.getD (∅, ∅)

/-
Applies a transfomation to a specified image of `slot` and `inst`.
If the image is not yet defined, applies the transformation to `(∅, ∅)`.
-/
def modify (m : InstMap) (slot : Nat) (inst : Expr)
    (f : (PHashSet PartialMatch × PHashSet FVarId) → PHashSet PartialMatch × PHashSet FVarId) :
    InstMap :=
  { map := m.map.insert slot
     ((m.map.findD slot .empty).insert inst (f (m.findD slot inst))) }

/-TODO: Do we need to connect `inst` with `MetaM (Option Substitution)`?.-/

/-- The `slot` represents the input hypothesis corresponding to `hyp`-/
def insertHyp (m : InstMap) (slot : Nat) (inst : Expr) (hyp : FVarId) : InstMap :=
  m.modify slot inst (fun (ms, hs) ↦ (ms, hs.insert hyp))

/-- The `slot` represents the maximal input hypothesis in `partialMatch`-/
def insertPartialMatches (m : InstMap) (slot : Nat) (inst : Expr)
    (partialMatch : PartialMatch) : InstMap :=
  if partialMatch.level == slot then
    m.modify slot inst (fun (ms, hs) ↦ (ms.insert partialMatch, hs))
  else panic! "Level of match is not maximal"

/- Note :
The for-loop in this function could probably be converted into a fold, but I think this would make
the code really hard to read. it would probably make it faster so worth a revisit for optimisation.
-/
/--
Remove a hyp from a `InstMap`.
Process is:
1. removes `hyp` at `hyp`'s associated slot,
2. removes all `PartialMatches` that contain `hyp` for all slot GE the associated slot.
-/
def removeHyp (m : InstMap) (hyp : FVarId) (slot : Nat) : MetaM InstMap := do
  let mut imaps := m.map
  /- The fold here outputs the list of keys of `m.map`.-/
  for i in (m.map.foldl (fun (acc : List Nat) k _ => k :: acc) []).filter (slot ≤ ·) do
    /- We use `find!` since `i` comes from a subset of the keys of `m.map`. -/
    let mut maps := (m.map.find! i)
    /- We execute `hs.erase hyp` only when `i == slot`. -/
    if i == slot then
      maps := maps.foldl (fun m e (ms, hs) => m.insert e
        (ms.fold (fun ms m ↦ if m.hyps.contains hyp then ms.erase m else ms) ms, hs.erase hyp))
        maps
    else
      maps := maps.foldl (fun m e (ms, hs) => m.insert e
        (ms.fold (fun ms m ↦ if m.hyps.contains hyp then ms.erase m else ms) ms, hs))
        maps
    imaps := imaps.insert i maps
  return {map := imaps}
end InstMap

namespace VariableMap

def find (a : VariableMap) (var : MVarId) : InstMap :=
  a.map.find? var |>.getD ∅

def modify (a : VariableMap) (var : MVarId) (f : InstMap → InstMap) : VariableMap :=
  match a.map.find? var with
  | none => ∅
  | some m => ⟨a.map.insert var (f m)⟩

/-- Function that adds a hypothesis to the relevent InstMaps. These are the variables
found in `slot.common` where the input hypothesis associated to `slot` matches `hyp`.
This means that we can unify `slot.MVarId` to `hyp`. -/
def addHypToMaps (a : VariableMap) (slot : Slot) (subs : Substitution) (hyp : FVarId) :
    VariableMap := Id.run do
  let mut a := a
  for var in slot.common do
    a := a.modify var (·.insertHyp slot.index (subs.find? var |>.get!) hyp)
  return a

/-- Function that adds a match to the relevent InstMaps. If `lvl` is the level of the match,
then `slot.slot = lvl + 1` so the relevent `vars` are the common of the next slot. -/
def addMatchToMaps (a : VariableMap) (slot : Slot) (nextSlot : Slot)
    (subs : Substitution) (partialMatch : PartialMatch) : VariableMap := Id.run do
  let mut a := a
  for var in nextSlot.common do
    a := a.modify var (fun m => m.insertPartialMatches slot.index (subs.find? var |>.get!) partialMatch)
  return a

def removeHypInMaps (a : VariableMap) (hyp : FVarId) (slot : Nat ) : MetaM VariableMap :=
  return ⟨← a.map.mapM (fun vm ↦ vm.removeHyp hyp slot)⟩

/-- `slot` should not be the first slot. -/
def findPartialMatch (a : VariableMap) (slot : Slot) (subst : Substitution) :
    HashSet PartialMatch := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut pms : HashSet PartialMatch :=
      /-TODO: extract-/
      (a.find common[0]).findD (slot.index - 1) (subst.find? common[0] |>.get!)
        |>.1 |> PHashSet.toHashSet
    for var in common[1:] do
      pms := HashSet.inter pms
        <| PHashSet.toHashSet ((a.find var).findD (slot.index - 1) (subst.find? var |>.get!) |>.1)
    return pms
  else
    panic! "findPartialMatch: common variable array is empty."

/-- Precondition: slot is not the last slot. -/
def findHypotheses (a : VariableMap) (slot : Slot) (subst : Substitution) : HashSet FVarId :=
  Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps : HashSet FVarId :=
      /-TODO: extract-/
      (a.find common[0]).findD (slot.index + 1) (subst.find? common[0] |>.get!)
        |>.2 |> PHashSet.toHashSet
    for var in common[1:] do
      hyps := HashSet.inter hyps
        <| PHashSet.toHashSet ((a.find var).findD (slot.index + 1) (subst.find? var |>.get!) |>.2)
    return hyps
  else
    panic! "findHypotheses: common variable array is empty."

end VariableMap

namespace RuleState

/-- Precondition: The `slot` represents the maximal input hypothesis in `partialMatch`.
This means that `m.level = slot.slot`.
-/
partial def addMatch (r : RuleState) (slot : Slot) (m : PartialMatch) :
    MetaM (RuleState × Array Expr) := do
  let subst := m.subst
  let mut r := r
  let mut fullMatches : Array Expr := ∅
  if r.slots.size == slot.index then
    match ← r.reconstruct m with
    | none => panic! "Reconstruct failed to provide an expression"
    | some expr => return ⟨r, #[expr]⟩
  else
    r := { r with
      variableMap :=
        r.variableMap.addMatchToMaps slot (r.slot! (slot.index + 1)) subst m
    }
    for hyp in r.variableMap.findHypotheses slot subst do
      let x ← r.addMatch slot ⟨hyp :: m.hyps, subst, slot.index + 1⟩
      r := x.1
      fullMatches := fullMatches.append x.2
    return ⟨r, fullMatches⟩

/-- Precondition: The `slot` represents the input hypothesis corresponding to `h` -/
def addHypothesis (r : RuleState) (slot : Slot) (h : FVarId) :
    MetaM (RuleState × Array Expr) := do
  match ← r.matchInputHypothesis? slot.index h with
  | none => panic! "The rule should have a non-trivial substitution at every slot."
  | some subst =>
    let mut r :=
      { r with variableMap := r.variableMap.addHypToMaps slot subst h }
    let mut fullMatches : Array Expr := ∅
    if slot.index == 0 then
      return ← r.addMatch slot ⟨[h], subst, 0⟩
    else
      for pm in r.variableMap.findPartialMatch slot subst do
        let subst := pm.subst.foldl (init := subst) λ subst k v =>
          assert! let r := subst.find? k; r == none || r == some v
          subst.insert k v
        /- We add `hyp` at the beginning, update relevant insts and the level. -/
        let x ← r.addMatch slot ⟨h :: pm.hyps, subst, slot.index⟩
        r := x.1
        fullMatches := fullMatches.append x.2
      return ⟨r, fullMatches⟩

end RuleState

open Lean Lean.Meta

inductive Prio : Type where
  | normsafe (n : Int) : Prio
  | «unsafe» (p : Percent) : Prio
  deriving Inhabited

structure ForwardRule where
  name : RuleName
  expr : Expr
  prio : Prio
  deriving Inhabited

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
  tree : DiscrTree (ForwardRule × Nat)
  deriving Inhabited

namespace ForwardIndex

/- Insert the input hypotheses (and only the input hypotheses) of the rule in the index. -/
def insert (r : ForwardRule) (idx : ForwardIndex) : MetaM ForwardIndex := do
  let type ← inferType r.expr
  withReducible do
    forallTelescopeReducing type λ args _ => do
      let args ← args.mapM fun expr : Expr => do
        let type ← expr.mvarId!.getType
        let deps ← getMVars type
        return (expr, HashSet.ofArray deps)
      let mut tree := idx.tree
      let mut previousDeps : HashSet MVarId := HashSet.empty
      for h : i in [:args.size] do
        let (arg, deps) := args[i]
        previousDeps := previousDeps.insertMany deps
        if ! previousDeps.contains arg.mvarId! then do
          tree ← tree.insert arg (r, i) discrTreeConfig
      return ⟨tree⟩

def get (idx : ForwardIndex) (e : Expr) : MetaM (Array (ForwardRule × Nat)) :=
  idx.tree.getUnify e discrTreeConfig

end ForwardIndex

section ForwardState

structure QueueEntry where
  expr : Expr
  prio : Prio
  deriving Inhabited

/- Int with higher number is worse-/
/- Percentage with higher number is better-/
def QueueEntry.le (q₁ q₂ : QueueEntry) : Bool :=
  match q₁.prio, q₂.prio with
  | .normsafe x, .normsafe y => x ≤ y
  | .unsafe x, .unsafe y => x ≥ y
  | _, _ => panic! "comparing QueueEntries with different priority types"

structure ForwardState where
  /-- Map from the rule's `RuleName` to it's `RuleState`-/
  ruleStates : HashMap RuleName RuleState
  /-- The index of Forward Rule to be unified against. -/
  /- TODO: pull out of the ForwardState. -/
  index : ForwardIndex
  /- Arrays of complete matches.-/
  normQueue : BinomialHeap QueueEntry QueueEntry.le
  safeQueue : BinomialHeap QueueEntry QueueEntry.le
  unsafeQueue : BinomialHeap QueueEntry QueueEntry.le
  /- Map from hypotheses to -/
/-TODO? : FVarId → RuleName, slot, instantiation-/
 deriving Inhabited

/- Index can also give the `Expr` of which rule it thinks we should look at
and the slot `i` associated to the hypothesis.-/
def ForwardState.addHypothesis (h : FVarId) (forwardState : ForwardState) :
    MetaM ForwardState := do
  let mut forwardState := forwardState
  for (r, i) in ← forwardState.index.get (← h.getType) do
    let RS ← match forwardState.ruleStates.find? r.name with
      | some n => pure n
      | none => RuleState.ofExpr r.expr
    let slot ← match RS.slots.find? (fun s => s.hypIndex = i) with
    | none => throwError "Positions in index should match the slots' positions"
    | some slot => pure slot
    let (RS, Arr) ← RS.addHypothesis slot h
    forwardState := {
      forwardState with
      ruleStates := forwardState.ruleStates.insert r.name RS
    }
    match r.name.phase with
    | .norm =>
      for expr in Arr do
        forwardState := {
          forwardState with
          normQueue := forwardState.normQueue.insert {expr, prio := r.prio}
        }
    | .safe =>
      for expr in Arr do
        forwardState := {
          forwardState with
          safeQueue := forwardState.safeQueue.insert {expr, prio := r.prio}
        }
    | .«unsafe» =>
      for expr in Arr do
        forwardState := {
          forwardState with
          unsafeQueue := forwardState.unsafeQueue.insert {expr, prio := r.prio}
        }
  /- Return updated map-/
  return forwardState

/- Question : Do we need to update the queues?-/
def ForwardState.removeHypothesis (h : FVarId) (forwardState : ForwardState) :
    MetaM ForwardState := do
  let mut forwardState := forwardState
  for (r, i) in ← forwardState.index.get (← h.getType) do
    let RS ← match forwardState.ruleStates.find? r.name with
      | some n => pure n
      | none => RuleState.ofExpr r.expr
    /-Here `RS` is some `RuleState` that contains some hyp with the same type as `h`.
    It should be associated to a slot via `i` and `hypIndex`.-/
    /- `i` is associated to one of the slot's hypIndices. We want the slot.-/
    let slot := RS.slots.foldl (fun n s ↦ if s.hypIndex == i then s.index else n) 0
    /- We need to update the `atlas` of `RS`-/
    let mut RS :=
      { RS with variableMap := ← RS.variableMap.removeHypInMaps h slot }
    forwardState := {
      forwardState with
      ruleStates := forwardState.ruleStates.insert r.name RS}
  /- Return updated map-/
  return forwardState

/-- Returns the queue of safe rules. -/
def ForwardState.popNormRule (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.normQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)

/-- Returns the queue of safe rules. -/
def ForwardState.popSafeRule (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.safeQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)

/-- Returns the queue of safe rules. -/
def ForwardState.popUnsafeRule (forwardState : ForwardState) :
    Option (Expr × BinomialHeap QueueEntry QueueEntry.le) :=
  match forwardState.unsafeQueue.deleteMin with
  | none => none
  | some (q, bh) => (q.expr, bh)

end Aesop.ForwardState
