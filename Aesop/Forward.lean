/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Percent
import Batteries.Data.BinomialHeap.Basic
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

structure SlotIndex where
  toNat : Nat
  deriving Inhabited, BEq, Hashable, DecidableEq

instance : LT SlotIndex where
  lt i j := i.toNat < j.toNat

instance : DecidableRel (α := SlotIndex) (· < ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat < j.toNat)

instance : LE SlotIndex where
  le i j := i.toNat ≤ j.toNat

instance : DecidableRel (α := SlotIndex) (· ≤ ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat ≤ j.toNat)

instance : HAdd SlotIndex Nat SlotIndex where
  hAdd i j := ⟨i.toNat + j⟩

instance : HSub SlotIndex Nat SlotIndex where
  hSub i j := ⟨i.toNat - j⟩

structure PremiseIndex where
  toNat : Nat
  deriving Inhabited, BEq, Hashable, DecidableEq

instance : LT PremiseIndex where
  lt i j := i.toNat < j.toNat

instance : DecidableRel (α := PremiseIndex) (· < ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat < j.toNat)

instance : LE PremiseIndex where
  le i j := i.toNat ≤ j.toNat

instance : DecidableRel (α := PremiseIndex) (· ≤ ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat ≤ j.toNat)

instance : ToString PremiseIndex where
  toString i := toString i.toNat

structure Slot where
  /-- Metavariable representing the premise of this slot. -/
  mvarId : MVarId
  /-- Index of the slot. Slots are always part of a list of slots, and `index`
  is the 0-based index of this slot in that list. -/
  index : SlotIndex
  /-- The previous premises that the premise of this slot depends on. -/
  deps : HashSet MVarId
  /-- Common variables shared between this slot and the previous slots. -/
  common : HashSet MVarId
  /-- 0-based index of the premise represented by this slot in the rule type. -/
  premiseIndex : PremiseIndex
  deriving Inhabited

abbrev Substitution := AssocList MVarId Expr

structure Match where
  hyps : List FVarId
  subst : Substitution
  deriving Inhabited

namespace Match

instance : BEq Match where
  beq m₁ m₂ := m₁.hyps == m₂.hyps

instance : Hashable Match where
  hash m := hash m.hyps

/--
The level of a match `m` is the greatest slot index `i` such that `m` associates
a hypothesis to slot `i`. It is `none` if the match is empty.
-/
def level? (m : Match) : Option SlotIndex :=
  if m.hyps.isEmpty then none else some ⟨m.hyps.length - 1⟩

end Match

/-- Partial matches associated with a particular slot instantiation. An entry
`s ↦ i ↦ (ms, hs)` indicates that for the instantiation `i` of slot `s`, we have
partial matches `ms` containing hypotheses `hs`. -/
structure InstMap where
  map : PHashMap SlotIndex (PHashMap Expr (PHashSet Match × PHashSet FVarId))
  deriving Inhabited

namespace InstMap

instance : EmptyCollection InstMap := ⟨⟨.empty⟩⟩

@[inline]
def find? (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    Option (PHashSet Match × PHashSet FVarId) :=
  imap.map.find? slot |>.bind λ slotMap => slotMap.find? inst

@[inline]
def findD (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    PHashSet Match × PHashSet FVarId :=
  imap.find? slot inst |>.getD (∅, ∅)

/-
Applies a transfomation to a specified image of `slot` and `inst`.
If the image is not yet defined, applies the transformation to `(∅, ∅)`.
-/
def modify (imap : InstMap) (slot : SlotIndex) (inst : Expr)
    (f : PHashSet Match → PHashSet FVarId → PHashSet Match × PHashSet FVarId) :
    InstMap :=
  let (ms, hyps) := imap.findD slot inst
  let slotMap := imap.map.findD slot .empty |>.insert inst (f ms hyps)
  ⟨imap.map.insert slot slotMap⟩

/-TODO: Do we need to connect `inst` with `MetaM (Option Substitution)`?.-/

/-- The `slot` represents the input hypothesis corresponding to `hyp`-/
def insertHyp (imap : InstMap) (slot : SlotIndex) (inst : Expr) (hyp : FVarId) :
    InstMap :=
  imap.modify slot inst fun ms hs ↦ (ms, hs.insert hyp)

/-- The `slot` represents the maximal input hypothesis in `m`-/
def insertMatch (imap : InstMap) (slot : SlotIndex) (inst : Expr) (m : Match) :
    InstMap :=
  imap.modify slot inst fun ms hs ↦ (ms.insert m, hs)

/--
Remove a hyp from an `InstMap`.
Process is:
1. removes `hyp` at `hyp`'s associated slot,
2. removes all `Matches` that contain `hyp` for all slot GE the associated slot.
-/
def removeHyp (imap : InstMap) (hyp : FVarId) (slot : SlotIndex) : InstMap := Id.run do
  let mut imaps := imap.map
  /- The fold here outputs the list of keys of `m.map`.-/
  let previousSlots : List SlotIndex :=
    imap.map.foldl (init := []) λ acc slot' _ =>
      if slot ≤ slot' then slot' :: acc else acc
  for i in previousSlots do
    /- We use `find!` since `i` comes from a subset of the keys of `m.map`. -/
    let mut maps := imap.map.find! i
    /- We execute `hs.erase hyp` only when `i == slot`. -/
    if i == slot then
      maps := maps.foldl (init := maps) fun m e (ms, hs) => m.insert e
        (ms.fold (fun ms m ↦ if m.hyps.contains hyp then ms.erase m else ms) ms, hs.erase hyp)
    else
      maps := maps.foldl (init := maps) fun m e (ms, hs) => m.insert e
        (ms.fold (fun ms m ↦ if m.hyps.contains hyp then ms.erase m else ms) ms, hs)
    imaps := imaps.insert i maps
  return {map := imaps}

end InstMap

/-- Map from variables to the partial matches of slots whose types contain the
variables. -/
structure VariableMap where
  map : PHashMap MVarId InstMap
  deriving Inhabited

namespace VariableMap

instance : EmptyCollection VariableMap :=
  ⟨⟨.empty⟩⟩

def find (vmap : VariableMap) (var : MVarId) : InstMap :=
  vmap.map.find? var |>.getD ∅

def modify (vmap : VariableMap) (var : MVarId) (f : InstMap → InstMap) :
    VariableMap :=
  match vmap.map.find? var with
  | none => vmap
  | some m => ⟨vmap.map.insert var (f m)⟩

/-- Function that adds a hypothesis to the relevent InstMaps. These are the variables
found in `slot.common` where the input hypothesis associated to `slot` matches `hyp`.
This means that we can unify `slot.MVarId` to `hyp`. -/
def addHypToMaps (vmap : VariableMap) (slot : Slot) (subs : Substitution)
    (hyp : FVarId) : VariableMap := Id.run do
  let mut vmap := vmap
  for var in slot.common do
    vmap := vmap.modify var (·.insertHyp slot.index (subs.find? var |>.get!) hyp)
  return vmap

/-- Function that adds a match to the relevent InstMaps. If `lvl` is the level of the match,
then `slot.slot = lvl + 1` so the relevent `vars` are the common of the next slot. -/
def addMatchToMaps (vmap : VariableMap) (slot : Slot) (nextSlot : Slot)
    (m : Match) : VariableMap := Id.run do
  let mut vmap := vmap
  for var in nextSlot.common do
    vmap :=
      vmap.modify var (·.insertMatch slot.index (m.subst.find? var |>.get!) m)
  return vmap

def removeHyp (vmap : VariableMap) (hyp : FVarId) (slot : SlotIndex) :
    VariableMap :=
  ⟨vmap.map.map (·.removeHyp hyp slot)⟩

/-- `slot` should not be the first slot. -/
def findMatch (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    HashSet Match := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut pms :=
      /-TODO: extract-/
      vmap.find common[0]
        |>.findD (slot.index - 1) (subst.find? common[0] |>.get!)
        |>.1 |> PHashSet.toHashSet
    for var in common[1:] do
      pms := HashSet.inter pms
        <| PHashSet.toHashSet (vmap.find var |>.findD (slot.index - 1) (subst.find? var |>.get!) |>.1)
    return pms
  else
    panic! "findMatch: common variable array is empty."

/-- Precondition: slot is not the last slot. -/
def findHypotheses (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    HashSet FVarId := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps : HashSet FVarId :=
      /-TODO: extract-/
      vmap.find common[0]
        |>.findD (slot.index + 1) (subst.find? common[0] |>.get!)
        |>.2 |> PHashSet.toHashSet
    for var in common[1:] do
      hyps := HashSet.inter hyps
        <| PHashSet.toHashSet (vmap.find var |>.findD (slot.index + 1) (subst.find? var |>.get!) |>.2)
    return hyps
  else
    panic! "findHypotheses: common variable array is empty."

end VariableMap

structure RuleState where
  /-- Expression of the associated theorem. -/
  expr : Expr
  /-- Number of premises of the rule. -/
  numPremises : Nat
  /-- Slots representing each of the maximal premises. For each index
  `i` of `slots`, `slots[i].index = i`. -/
  slots : Array Slot
  /-- The conclusion of the rule. -/
  conclusion : Expr
  /-- MetaState in which slots and conclusion are valid-/
  metaState : Meta.SavedState
  /-- Variable map. -/
  variableMap : VariableMap
  deriving Nonempty

namespace RuleState

def ofExpr (thm : Expr) : MetaM RuleState := withoutModifyingState do
  let e ← inferType thm
  let ⟨args, _, conclusion⟩ ← forallMetaTelescope e
  let metaState ← saveState
  let args ← args.mapM fun expr : Expr => do
    let type ← expr.mvarId!.getType
    let deps ← getMVars type
    return (expr.mvarId!, HashSet.ofArray deps)
  let mut slots : Array Slot := Array.mkEmpty args.size
  let mut previousDeps := HashSet.empty
  for h : i in [:args.size] do
    let (mvarId, deps) := args[i]'h.2
    let commonDeps := HashSet.inter previousDeps deps
    /- We update `slot = 0` with correct ordering later (see **) -/
    slots := slots.push ⟨mvarId, ⟨0⟩, deps, commonDeps, ⟨i⟩⟩
    previousDeps := previousDeps.insertMany deps
  let numPremises := slots.size
  /- Filtering out non-input hypetheses-/
  slots := slots.filter fun slot => ! previousDeps.contains slot.mvarId
  /- (**) Assigns ordering of slots -/
  slots := slots.mapIdx fun index current => {current with index := ⟨index⟩}
  return {
    expr := thm
    variableMap := ∅
    numPremises, slots, metaState, conclusion
  }

@[macro_inline]
def slot! (rs : RuleState) (slot : SlotIndex) : Slot :=
  rs.slots[slot.toNat]!

/-- `r.slot! slot` contains the information concerning the inputHypothesis. We match this
with a given `hyp`.-/
def matchInputHypothesis? (rs : RuleState) (slot : SlotIndex) (hyp : FVarId) :
    MetaM (Option Substitution) := do
  let slot := rs.slot! slot
  rs.metaState.runMetaM' do
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
/-- Function reconstructing a rule from a match. -/
def reconstruct (rs : RuleState) (m : Match) : MetaM Expr := do
  if m.level?.map (·.toNat) != some (rs.slots.size - 1) then
    throwError "level of match is not maximal"
  else
    let sortedSlots :=
      rs.slots.qsort fun s₁ s₂ ↦ s₁.premiseIndex < s₂.premiseIndex
    let mut arr := Array.mkArray rs.numPremises none
    let mut hyps := m.hyps
    for slot in sortedSlots do
      hyps := hyps.drop 1
      arr := arr.set! slot.premiseIndex.toNat (some <| .fvar hyps.head!)
    mkAppOptM' rs.expr arr

/-- Precondition: The `slot` represents the maximal input hypothesis in `m`.
This means that `m.level = slot.index`.
-/
partial def addMatch (rs : RuleState) (slot : Slot) (m : Match) :
    MetaM (RuleState × Array Expr) := do
  let mut rs := rs
  let mut fullMatches : Array Expr := ∅
  if slot.index.toNat == rs.slots.size - 1 then
    return ⟨rs, #[← rs.reconstruct m]⟩
  else
    rs := { rs with
      variableMap :=
        rs.variableMap.addMatchToMaps slot (rs.slot! (slot.index + 1)) m
    }
    for hyp in rs.variableMap.findHypotheses slot m.subst do
      let (newRs, newFullMatches) ←
        rs.addMatch slot ⟨hyp :: m.hyps, m.subst⟩
      rs := newRs
      fullMatches := fullMatches ++ newFullMatches
    return ⟨rs, fullMatches⟩

/-- Precondition: The `slot` represents the input hypothesis corresponding to `h` -/
def addHypothesis (rs : RuleState) (slot : Slot) (h : FVarId) :
    MetaM (RuleState × Array Expr) := do
  match ← rs.matchInputHypothesis? slot.index h with
  | none => panic! "The rule should have a non-trivial substitution at every slot."
  | some subst =>
    let mut r :=
      { rs with variableMap := rs.variableMap.addHypToMaps slot subst h }
    let mut fullMatches : Array Expr := ∅
    if slot.index.toNat == 0 then
      return ← r.addMatch slot ⟨[h], subst⟩
    else
      for pm in r.variableMap.findMatch slot subst do
        let subst := pm.subst.foldl (init := subst) λ subst k v =>
          assert! let r := subst.find? k; r == none || r == some v
          subst.insert k v
        /- We add `hyp` at the beginning, update relevant insts and the level. -/
        let x ← r.addMatch slot ⟨h :: pm.hyps, subst⟩
        r := x.1
        fullMatches := fullMatches.append x.2
      return ⟨r, fullMatches⟩

end RuleState

inductive Prio : Type where
  | normSafe (n : Int) : Prio
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
Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`,
`i : PremiseIndex` and the `i`-th argument of the type of `r.expr` (counting
from zero) likely unifies with `T`.
-/
structure ForwardIndex where
  tree : DiscrTree (ForwardRule × PremiseIndex)
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
          tree ← tree.insert arg (r, ⟨i⟩) discrTreeConfig
      return ⟨tree⟩

def get (idx : ForwardIndex) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  idx.tree.getUnify e discrTreeConfig

end ForwardIndex

structure ForwardStateQueueEntry where
  expr : Expr
  prio : Prio
  deriving Inhabited

namespace ForwardStateQueueEntry

/- Int with higher number is worse-/
/- Percentage with higher number is better-/
protected def le (q₁ q₂ : ForwardStateQueueEntry) : Bool :=
  match q₁.prio, q₂.prio with
  | .normSafe x, .normSafe y => x ≤ y
  | .unsafe x, .unsafe y => x ≥ y
  | _, _ => panic! "comparing QueueEntries with different priority types"

end ForwardStateQueueEntry

abbrev ForwardStateQueue :=
  BinomialHeap ForwardStateQueueEntry ForwardStateQueueEntry.le

structure ForwardState where
  /-- Map from the rule's `RuleName` to it's `RuleState`-/
  ruleStates : PHashMap RuleName RuleState
  /-- Queues of complete matches. -/
  normQueue : ForwardStateQueue
  safeQueue : ForwardStateQueue
  unsafeQueue : ForwardStateQueue
 deriving Inhabited

namespace ForwardState

def addHypothesis (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : MetaM ForwardState := do
  let mut fs := fs
  for (r, i) in ms do
    let rs ← fs.ruleStates.find? r.name |>.getDM (RuleState.ofExpr r.expr)
    let some slot := rs.slots.find? (·.premiseIndex == i)
      | throwError "addHypothesis: internal error: no slot with hyp index {i} for rule {r.name}"
    let (rs, fullMatches) ← rs.addHypothesis slot h
    fs := { fs with ruleStates := fs.ruleStates.insert r.name rs }
    for expr in fullMatches do
      fs := addFullMatch expr r fs
  return fs
where
  addFullMatch (expr : Expr) (r : ForwardRule) (fs : ForwardState) :
      ForwardState :=
    let queueEntry := { expr, prio := r.prio }
    match r.name.phase with
    | .norm   => { fs with normQueue := fs.normQueue.insert queueEntry }
    | .safe   => { fs with safeQueue := fs.safeQueue.insert queueEntry }
    | .unsafe => { fs with unsafeQueue := fs.unsafeQueue.insert queueEntry }

/- TODO: also update the queues -/
def removeHypothesis (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : ForwardState := Id.run do
  let mut fs := fs
  for (r, i) in ms do
    let some rs := fs.ruleStates.find? r.name
      | continue
    let some slot := rs.slots.find? (·.premiseIndex == i)
      | panic! "no slot with hyp index {i} for rule {r.name}"
    let variableMap := rs.variableMap.removeHyp h slot.index
    fs := { fs with
      ruleStates := fs.ruleStates.insert r.name { rs with variableMap }
    }
  return fs

def popFirstNormMatch (fs : ForwardState) : Option (Expr × ForwardState) :=
  match fs.normQueue.deleteMin with
  | none => none
  | some (entry, normQueue) => (entry.expr, { fs with normQueue })

def popFirstSafeMatch (fs : ForwardState) : Option (Expr × ForwardState) :=
  match fs.safeQueue.deleteMin with
  | none => none
  | some (entry, safeQueue) => (entry.expr, { fs with safeQueue })

def popFirstUnsafeMatch (fs : ForwardState) : Option (Expr × ForwardState) :=
  match fs.unsafeQueue.deleteMin with
  | none => none
  | some (entry, unsafeQueue) => (entry.expr, { fs with unsafeQueue })

end Aesop.ForwardState
