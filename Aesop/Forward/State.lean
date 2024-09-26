/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Rule.Forward
import Batteries.Lean.Meta.SavedState
import Batteries.Data.BinomialHeap.Basic

open Lean Lean.Meta
open Batteries (BinomialHeap)

namespace Aesop

/-- A substitution maps premise metavariables to assignments. -/
abbrev Substitution := AssocList MVarId Expr

structure Match where
  /-- Hyps for each slot, in reverse order. If there are `n` slots, the `i`th
  hyp in `revHyps` is the hyp associated with the slot with index `n - i`. -/
  revHyps : List FVarId
  revHyps_ne : 0 < revHyps.length := by simp
  /-- The substitution induced by the assignment of the hyps in `hyps` to the
  rule's slots. -/
  subst : Substitution

namespace Match

instance : Inhabited Match :=
  ⟨{ revHyps := [default], subst := ∅ }⟩

instance : BEq Match where
  beq m₁ m₂ := m₁.revHyps == m₂.revHyps

instance : Hashable Match where
  hash m := hash m.revHyps

/--
The level of a match `m` is the greatest slot index `i` such that `m` associates
a hypothesis to slot `i`.
-/
def level (m : Match) : SlotIndex :=
  ⟨m.revHyps.length - 1⟩

/-- Given a complete match `m` for `r`, produce an application of the theorem
`r.expr` to the hypotheses from `m`. -/
def reconstruct (r : ForwardRule) (m : Match) : Expr := Id.run do
  let hyps := m.revHyps.toArray.reverse
  if hyps.size != r.slots.size then
    panic! s!"match is not complete; slots: {r.slots.size}; match hyps: {hyps.size}"
  let slots :=
    r.slots.qsort (λ s₁ s₂ => s₁.premiseIndex < s₂.premiseIndex) |>.zip hyps
  let mut args := Array.mkEmpty r.premises.size
  let mut slotIdx := 0
  for h : i in [:r.premises.size] do
    if let some (slot, hyp) := slots[slotIdx]? then
      if slot.premiseIndex.toNat == i then
        args := args.push (.fvar hyp)
        slotIdx := slotIdx + 1
        continue
    let premise := r.premises[i]
    let some inst := m.subst.find? premise
      | panic! s!"no hyp or instantiation for premise {premise.name}"
    args := args.push inst
  return mkAppN r.expr args

end Match

/-- Partial matches associated with a particular slot instantiation. An entry
`s ↦ e ↦ (ms, hs)` indicates that for the instantiation `e` of slot `s`, we have
partial matches `ms` and hypotheses `hs`. -/
structure InstMap where
  map : PHashMap SlotIndex (PHashMap Expr (PHashSet Match × PHashSet FVarId))
  deriving Inhabited

namespace InstMap

instance : EmptyCollection InstMap := ⟨⟨.empty⟩⟩

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`. -/
@[inline]
def find? (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    Option (PHashSet Match × PHashSet FVarId) :=
  imap.map.find? slot |>.bind λ slotMap => slotMap.find? inst

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`, or `(∅, ∅)` if `slot` and `inst` do not have any
associated matches. -/
@[inline]
def findD (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    PHashSet Match × PHashSet FVarId :=
  imap.find? slot inst |>.getD (∅, ∅)

/-- Applies a transfomation to the data associated to `slot` and `inst`.
If the there is no such data, the transformation is applied to `(∅, ∅)`. -/
def modify (imap : InstMap) (slot : SlotIndex) (inst : Expr)
    (f : PHashSet Match → PHashSet FVarId → PHashSet Match × PHashSet FVarId) :
    InstMap :=
  let (ms, hyps) := imap.findD slot inst
  let slotMap := imap.map.findD slot .empty |>.insert inst (f ms hyps)
  ⟨imap.map.insert slot slotMap⟩

/-- Inserts a hyp associated with slot `slot` and instantiation `inst`.
The hyp should be a valid assignment for the slot's premise. -/
def insertHyp (imap : InstMap) (slot : SlotIndex) (inst : Expr) (hyp : FVarId) :
    InstMap :=
  imap.modify slot inst fun ms hs ↦ (ms, hs.insert hyp)

/-- Inserts a match associated with slot `slot` and instantiation `inst`.
The match's level should be equal to `slot`. -/
def insertMatchCore (imap : InstMap) (slot : SlotIndex) (inst : Expr)
    (m : Match) : InstMap :=
  imap.modify slot inst fun ms hs ↦ (ms.insert m, hs)

/-- Inserts a match. The match `m` is associated with the slot given by its
level (i.e., the maximal slot for which `m` contains a hypothesis) and the
instantiation of `var` given by the map's substitution. -/
def insertMatch (imap : InstMap) (var : MVarId) (m : Match) :
    InstMap := Id.run do
  let some inst := m.subst.find? var
    | panic! s!"variable {var.name} is not assigned in substitution"
  imap.insertMatchCore m.level inst m

/-- Remove `hyp` from slots starting at `slot`. For each mapping
`s ↦ e ↦ (ms, hs)` in `imap`, if `s ≥ slot`, then `hyp` is removed from `hs` and
any matches containing `hyp` are removed from `ms`. -/
def eraseHyp (imap : InstMap) (hyp : FVarId) (slot : SlotIndex) : InstMap := Id.run do
  let mut imaps := imap.map
  let nextSlots : List SlotIndex :=
    imap.map.foldl (init := []) λ acc slot' _ =>
      if slot ≤ slot' then slot' :: acc else acc
  for i in nextSlots do
    let maps := imap.map.find! i
    let maps := maps.foldl (init := maps) fun m e (ms, hs) =>
      let ms := PersistentHashSet.filter (·.revHyps.contains hyp) ms
      m.insert e (ms, hs.erase hyp)
    imaps := imaps.insert i maps
  return { map := imaps }

end InstMap

/-- Map from variables to the matches and hypotheses of slots whose types
contain the variables. -/
structure VariableMap where
  map : PHashMap MVarId InstMap
  deriving Inhabited

namespace VariableMap

instance : EmptyCollection VariableMap :=
  ⟨⟨.empty⟩⟩

/-- Get the `InstMap` associated with a variable. -/
def find? (vmap : VariableMap) (var : MVarId) : Option InstMap :=
  vmap.map.find? var

/-- Get the `InstMap` associated with a variable, or an empty `InstMap`. -/
def find (vmap : VariableMap) (var : MVarId) : InstMap :=
  vmap.find? var |>.getD ∅

/-- Modify the `InstMap` associated to variable `var`. If no such `InstMap`
exists, the function `f` is applied to the empty `InstMap` and the result is
associated with `var`. -/
def modify (vmap : VariableMap) (var : MVarId) (f : InstMap → InstMap) :
    VariableMap :=
  match vmap.map.find? var with
  | none => ⟨vmap.map.insert var (f ∅)⟩
  | some m => ⟨vmap.map.insert var (f m)⟩

/-- Add a hypothesis `hyp`. Precondition: `hyp` matches the premise of slot
`slot` with substitution `sub` (and hence `sub` contains a mapping for each
variable in `slot.common`). -/
def addHyp (vmap : VariableMap) (slot : Slot) (sub : Substitution)
    (hyp : FVarId) : VariableMap :=
  slot.common.fold (init := vmap) λ vmap var =>
    vmap.modify var (·.insertHyp slot.index (sub.find? var |>.get!) hyp)

/-- Add a match `m`. Precondition: `nextSlot` is the slot with index
`m.level + 1`. -/
def addMatch (vmap : VariableMap) (nextSlot : Slot) (m : Match) :
    VariableMap :=
  nextSlot.common.fold (init := vmap) λ vmap var =>
    vmap.modify var (·.insertMatch var m)

/-- Remove a hyp from `slot` and all following slots. -/
def eraseHyp (vmap : VariableMap) (hyp : FVarId) (slot : SlotIndex) :
    VariableMap :=
  ⟨vmap.map.map (·.eraseHyp hyp slot)⟩

/-- Find matches in slot `slot - 1` whose substitutions are compatible with
`subst`. Preconditions: `slot.index` is nonzero, `slot.common` is nonempty and
each variable contained in `slot.common` is also contained in `subst`. -/
def findMatches (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    HashSet Match := Id.run do
  if slot.index == ⟨0⟩ then
    panic! "slot has index 0"
  let common := slot.common.toArray
  if h : 0 < common.size then
    let firstVar := common[0]
    let mut ms := prevSlotMatches firstVar |> PersistentHashSet.toHashSet
    for var in common[1:] do
      let ms' := prevSlotMatches var
      ms := HashSet.filter ms (ms'.contains ·)
    return ms
  else
    panic! "no common variables"
where
  prevSlotMatches (var : MVarId) : PHashSet Match :=
    vmap.find var |>.findD (slot.index - 1) (subst.find? var |>.get!) |>.1

/-- Find hyps in `slot` whose substitutions are compatible with `subst`.
Precondition: `slot.common` is nonempty and each variable contained in it is
also contained in `subst`. -/
def findHyps (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    HashSet FVarId := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps := slotHyps common[0] |> PersistentHashSet.toHashSet
    for var in common[1:] do
      let hyps' := slotHyps var
      hyps := HashSet.filter hyps (hyps'.contains ·)
    return hyps
  else
    panic! "no common variables"
where
  slotHyps (var : MVarId) : PHashSet FVarId :=
    vmap.find var |>.findD slot.index (subst.find? var |>.get!) |>.2

end VariableMap

/-- Structure representing the state of one forward rule. -/
structure RuleState extends ForwardRuleInfo where
  /-- Variable map. -/
  variableMap : VariableMap
  deriving Nonempty

def ForwardRule.initialRuleState (r : ForwardRule) : RuleState :=
  { r.toForwardRuleInfo with variableMap := ∅ }

namespace RuleState

/-- Get the slot with the given index. Panic if the index is invalid. -/
@[macro_inline]
def slot! (rs : RuleState) (slot : SlotIndex) : Slot :=
  rs.slots[slot.toNat]!

/-- Match hypothesis `hyp` against the slot with index `slot` in `rs` (which
must be a valid index). -/
def matchInputHypothesis? (rs : RuleState) (slot : SlotIndex) (hyp : FVarId) :
    MetaM (Option Substitution) := do
  let slot := rs.slot! slot
  rs.metaState.runMetaM' do
    let inputHypType ← slot.mvarId.getType
    let hypType ← hyp.getType
    if ← isDefEq inputHypType hypType then
      /- Note: This was over `slot.common` and not `slot.deps`. We need `slot.deps`
      because, among other issues, `slot.common` is empty in the first slot. Even though
      we don't have dependencies, we still need to keep track of the subs of hyp.
      Otherwise, we would trigger the first panic in `AddHypothesis`.-/
      let mut subst : Substitution := ∅
      for var in slot.deps do
        let mvar := .mvar var
        let assignment ← instantiateMVars mvar
        if assignment == mvar then
          throwError "aesop: internal error: matchInputHypothesis?: while matching hyp {hyp.name}: no assignment for mvar {var.name}"
        subst := subst.insert var assignment
      return subst
    else
      return none

/-- Add a match to the rule state. -/
-- This function is just `partial`, but Lean doesn't realise that the return
-- type is inhabited.
unsafe def addMatchUnsafe (rs : RuleState) (m : Match) :
    RuleState × Array Match := Id.run do
  let mut rs := rs
  let mut fullMatches := #[]
  let slotIdx := m.level
  if slotIdx.toNat == rs.slots.size - 1 then
    return ⟨rs, #[m]⟩
  else
    let nextSlot := rs.slot! $ slotIdx + 1
    rs := { rs with
      variableMap := rs.variableMap.addMatch nextSlot m
    }
    for hyp in rs.variableMap.findHyps nextSlot m.subst do
      let m := { revHyps := hyp :: m.revHyps, subst := m.subst }
      let (newRs, newFullMatches) ← rs.addMatchUnsafe m
      rs := newRs
      fullMatches := fullMatches ++ newFullMatches
    return ⟨rs, fullMatches⟩

@[implemented_by addMatchUnsafe, inherit_doc addMatchUnsafe]
opaque addMatch (rs : RuleState) (m : Match) : RuleState × Array Match :=
  (rs, default)

/-- Add a hyp to the rule state. `subst` must be the substitution that results
from applying `h` to `slot`. -/
def addHypCore (rs : RuleState) (slot : Slot) (h : FVarId)
    (subst : Substitution) : RuleState × Array Match := Id.run do
  let mut rs :=
    { rs with variableMap := rs.variableMap.addHyp slot subst h }
  if slot.index.toNat == 0 then
    return ← rs.addMatch { revHyps := [h], subst }
  else
    let mut fullMatches := #[]
    for pm in rs.variableMap.findMatches slot subst do
      let subst := pm.subst.foldl (init := subst) λ subst k v =>
        assert! let r := subst.find? k; r == none || r == some v
        subst.insert k v
      let m := { revHyps := h :: pm.revHyps, subst }
      let (newRs, newFullMatches) ← rs.addMatch m
      rs := newRs
      fullMatches := fullMatches ++ newFullMatches
    return ⟨rs, fullMatches⟩

/-- Add a hypothesis to the rule state. If the hypothesis's type does not match
the premise corresponding to `slot`, then the hypothesis is not added.
Returns the new rule state and the proofs resulting from any matches that were
completed by `h`. -/
def addHyp (rs : RuleState) (slot : Slot) (h : FVarId) :
    MetaM (RuleState × Array Match) := do
  let some subst ← rs.matchInputHypothesis? slot.index h
    | return (rs, #[])
  return addHypCore rs slot h subst

end RuleState

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardStateQueueEntry where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : Match
  deriving Nonempty

namespace ForwardStateQueueEntry

/-- Compare two queue entries by rule priority. Higher-priority rules are
considered less (since the queues are min-queues). -/
protected def le (q₁ q₂ : ForwardStateQueueEntry) : Bool :=
  match q₁.rule.prio, q₂.rule.prio with
  | .normSafe x, .normSafe y => x ≤ y
  | .unsafe x, .unsafe y => x ≥ y
  | _, _ => panic! "comparing QueueEntries with different priority types"

/-- Build the proof corresponding to the complete match contained in `entry`. -/
def toProof (entry : ForwardStateQueueEntry) : Expr := Id.run do
  entry.match.reconstruct entry.rule

end ForwardStateQueueEntry

/-- A complete match queue. -/
abbrev ForwardStateQueue :=
  BinomialHeap ForwardStateQueueEntry ForwardStateQueueEntry.le

/-- State representing the (partial or complete) matches of a given set of
forward rules in a given local context. -/
structure ForwardState where
  /-- Map from each rule's `RuleName` to it's `RuleState`-/
  ruleStates : PHashMap RuleName RuleState
  /-- Queue of complete matches for norm rules. -/
  normQueue : ForwardStateQueue
  /-- Queue of complete matches for safe rules. -/
  safeQueue : ForwardStateQueue
  /-- Queue of complete matches for unsafe rules. -/
  unsafeQueue : ForwardStateQueue
  /-- Hypotheses that were removed from the local context. Matches containing
  such hyps are not removed from the complete match queues. Instead, they are
  added to this set and when a match is popped from the queues, we check whether
  it contains any removed hyps. -/
  erasedHyps : PHashSet FVarId
 deriving Inhabited

namespace ForwardState

/-- Add a hypothesis to the forward state. If `fs` represents a local context
`lctx`, then `fs.addHyp h ms` represents `lctx` with `h` added. `ms` must
overapproximate the rules for which `h` may unify with a maximal premise. -/
def addHyp (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : MetaM ForwardState := do
  let mut fs := fs
  for (r, i) in ms do
    let rs := fs.ruleStates.find? r.name |>.getD r.initialRuleState
    let some slot := rs.slots.find? (·.premiseIndex == i)
      | throwError "addHypothesis: internal error: no slot with hyp index {i} for rule {r.name}"
    let (rs, fullMatches) ← rs.addHyp slot h
    fs := { fs with ruleStates := fs.ruleStates.insert r.name rs }
    for m in fullMatches do
      fs := addFullMatch m r fs
  return fs
where
  addFullMatch («match» : Match) (r : ForwardRule) (fs : ForwardState) :
      ForwardState :=
    let queueEntry := { rule := r, «match» }
    match r.name.phase with
    | .norm   => { fs with normQueue := fs.normQueue.insert queueEntry }
    | .safe   => { fs with safeQueue := fs.safeQueue.insert queueEntry }
    | .unsafe => { fs with unsafeQueue := fs.unsafeQueue.insert queueEntry }

/-- Remove a hypothesis from the forward state. If `fs` represents a local
context `lctx`, then `fs.eraseHyp h ms` represents `lctx` with `h` removed. `ms`
must contain all rules for which `h` may unify with a maximal premise. -/
def eraseHyp (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : ForwardState := Id.run do
  let mut fs := { fs with erasedHyps := fs.erasedHyps.insert h }
  for (r, i) in ms do
    let some rs := fs.ruleStates.find? r.name
      | continue
    let some slot := rs.slots.find? (·.premiseIndex == i)
      | panic! s!"no slot with hyp index {i} for rule {r.name}"
    let variableMap := rs.variableMap.eraseHyp h slot.index
    fs := { fs with
      ruleStates := fs.ruleStates.insert r.name { rs with variableMap }
    }
  return fs

@[inline]
private partial def popFirstMatch? (fs : ForwardState)
    (queue : ForwardStateQueue) : Option (Expr × ForwardStateQueue) :=
  match queue.deleteMin with
  | none => none
  | some (entry, queue) =>
    if entry.match.revHyps.any (fs.erasedHyps.contains ·) then
      popFirstMatch? fs queue
    else
      (entry.toProof, queue)

/-- Get a proof for the first complete match of a norm rule. -/
def popFirstNormMatch? (fs : ForwardState) : Option (Expr × ForwardState) :=
  fs.popFirstMatch? fs.normQueue
    |>.map λ (e, q) => (e, { fs with normQueue := q })

/-- Get a proof for the first complete match of a safe rule. -/
def popFirstSafeMatch? (fs : ForwardState) : Option (Expr × ForwardState) :=
  fs.popFirstMatch? fs.safeQueue
    |>.map λ (e, q) => (e, { fs with safeQueue := q })

/-- Get a proof for the first complete match of an unsafe rule. -/
def popFirstUnsafeMatch? (fs : ForwardState) : Option (Expr × ForwardState) :=
  fs.popFirstMatch? fs.unsafeQueue
    |>.map λ (e, q) => (e, { fs with unsafeQueue := q })

end Aesop.ForwardState
