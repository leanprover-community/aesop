/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.Match

open Lean Lean.Meta
open ExceptToEmoji (toEmoji)

set_option linter.missingDocs true

namespace Aesop

private def ppPHashMap [BEq α] [Hashable α] [ToMessageData α]
    [ToMessageData β] (indent : Bool) (m : PHashMap α β) : MessageData :=
  flip MessageData.joinSep "\n" $
    m.foldl (init := []) λ xs a b =>
      let x :=
        if indent then
          m!"{a} =>{indentD $ toMessageData b}"
        else
          m!"{a} => {b}"
      x :: xs

private def ppPHashSet [BEq α] [Hashable α] [ToMessageData α] (s : PHashSet α) :
    MessageData :=
  toMessageData $ s.fold (init := #[]) λ as a => as.push a

/-- A hypothesis that has not yet been matched against a premise, or a rule
pattern substitution. -/
inductive RawHyp where
  /-- The hypothesis. -/
  | fvarId (fvarId : FVarId)
  /-- The rule pattern substitution. -/
  | patSubst (subst : Substitution)
  deriving Inhabited, BEq, Hashable

/-- A hypothesis that was matched against a premise, or a rule pattern
substitution. -/
structure Hyp where
  /-- The hypothesis, or `none` if this is a rule pattern substitution. -/
  fvarId? : Option FVarId
  /-- The substitution that results from matching the hypothesis against a
  premise or that was derived from the pattern. -/
  subst : Substitution
  deriving Inhabited

namespace Hyp

instance : BEq Hyp where
  beq h₁ h₂ :=
    match h₁.fvarId?, h₂.fvarId? with
    | some h₁, some h₂ => h₁ == h₂
    | none, none => h₁.subst == h₂.subst
    | _, _ => false

instance : Hashable Hyp where
  hash h :=
    match h.fvarId? with
    | some h => hash h
    | none => hash h.subst

/-- Returns `true` if `h` is the hyp `fvarId` or is a pattern substitution
containing `fvarId`. -/
def containsHyp (fvarId : FVarId) (h : Hyp) : Bool :=
  h.fvarId? == some fvarId || h.subst.containsHyp fvarId

/-- Does this `Hyp` represent a pattern substitution? -/
def isPatSubst (h : Hyp) : Bool :=
  h.fvarId?.isSome

end Hyp

set_option linter.missingDocs false in
/-- Partial matches associated with a particular slot instantiation. An entry
`s ↦ e ↦ (ms, hs)` indicates that for the instantiation `e` of slot `s`, we have
partial matches `ms` and hypotheses `hs`. -/
structure InstMap where
  map : PHashMap SlotIndex (PHashMap RPINF (PHashSet Match × PHashSet Hyp))
  deriving Inhabited

namespace InstMap

instance : EmptyCollection InstMap := ⟨⟨.empty⟩⟩

instance : ToMessageData InstMap where
  toMessageData m :=
    ppPHashMap (indent := true) $
      m.map.map λ instMap =>
        ppPHashMap (indent := false) $
          instMap.map λ (ms, hs) =>
            let hs : Array MessageData :=
              hs.fold (init := #[]) λ hs (h : Hyp) =>
                match h.fvarId? with
                | none => hs.push m!"{h.subst}"
                | some fvarId => hs.push m!"{Expr.fvar fvarId}"
            m!"{(ppPHashSet ms, hs)}"

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`. -/
@[inline]
def find? (imap : InstMap) (slot : SlotIndex) (inst : RPINF) :
    Option (PHashSet Match × PHashSet Hyp) :=
  imap.map.find? slot |>.bind λ slotMap => slotMap.find? inst

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`, or `(∅, ∅)` if `slot` and `inst` do not have any
associated matches. -/
@[inline]
def findD (imap : InstMap) (slot : SlotIndex) (inst : RPINF) :
    PHashSet Match × PHashSet Hyp :=
  imap.find? slot inst |>.getD (∅, ∅)

/-- Applies a transfomation to the data associated to `slot` and `inst`.
If there is no such data, the transformation is applied to `(∅, ∅)`. Returns the
new instantiation map and the result of `f`. -/
def modify (imap : InstMap) (slot : SlotIndex) (inst : RPINF)
    (f : PHashSet Match → PHashSet Hyp → PHashSet Match × PHashSet Hyp × α) :
    InstMap × α :=
  let (ms, hyps) := imap.findD slot inst
  let (ms, hyps, a) := f ms hyps
  let slotMap := imap.map.findD slot .empty |>.insert inst (ms, hyps)
  (⟨imap.map.insert slot slotMap⟩, a)

/-- Inserts a hyp associated with slot `slot` and instantiation `inst`.
The hyp must be a valid assignment for the slot's premise. Returns `true` if
the hyp was not previously associated with `slot` and `inst`. -/
def insertHyp (imap : InstMap) (slot : SlotIndex) (inst : RPINF) (hyp : Hyp) :
    InstMap × Bool :=
  imap.modify slot inst λ ms hs =>
    if hs.contains hyp then
      (ms, hs, false)
    else
      (ms, hs.insert hyp, true)

/-- Inserts a match associated with slot `slot` and instantiation `inst`.
The match's level must be `slot`. Returns `true` if the match was not previously
associated with `slot` and `inst`. -/
def insertMatchCore (imap : InstMap) (slot : SlotIndex) (inst : RPINF)
    (m : Match) : InstMap × Bool :=
  imap.modify slot inst λ ms hs =>
    if ms.contains m then
      (ms, hs, false)
    else
      (ms.insert m, hs, true)

/-- Inserts a match. The match `m` is associated with the slot given by its
level (i.e., the maximal slot for which `m` contains a hypothesis) and the
instantiation of `var` given by the map's substitution. Returns `true` if the
match was not previously associated with this slot and instantiation. -/
def insertMatch (imap : InstMap) (var : PremiseIndex) (m : Match) :
    InstMap × Bool := Id.run do
  let some inst := m.subst.find? var
    | panic! s!"variable {var} is not assigned in substitution"
  imap.insertMatchCore m.level inst m

/-- Modify the maps for slot `slot` and all later slots. -/
def modifyMapsForSlotsFrom (imap : InstMap) (slot : SlotIndex)
    (f : PHashSet Match → PHashSet Hyp → (PHashSet Match × PHashSet Hyp)) :
    InstMap := Id.run do
  let mut imaps := imap.map
  -- TODO Could remove this fold by passing the number of slots to this function.
  let nextSlots : Array SlotIndex :=
    imap.map.foldl (init := #[]) λ acc slot' _ =>
      if slot ≤ slot' then acc.push slot' else acc
  for i in nextSlots do
    let maps := imap.map.find! i |>.map λ (ms, hs) => f ms hs
    imaps := imaps.insert i maps
  return { map := imaps }

/-- Remove `hyp` from `slot` and all later slots. For each mapping
`s ↦ e ↦ (ms, hs)` in `imap`, if `s ≥ slot`, then `hyp` is removed from `hs` and
any matches containing `hyp` are removed from `ms`. -/
def eraseHyp (imap : InstMap) (hyp : FVarId) (slot : SlotIndex) :
    InstMap :=
  imap.modifyMapsForSlotsFrom slot λ ms hs =>
    let ms := PersistentHashSet.filter (·.containsHyp hyp) ms
    let hs := hs.erase { fvarId? := hyp, subst := default }
    (ms, hs)

/-- Remove the pattern substitution `subst` from `slot` and all later slots.
For each mapping `s ↦ e ↦ (ms, hs)` in `imap`, if `s ≥ slot`, then `subst` is
removed from `hs` and any matches containing `subst` are removed from `ms`. -/
def erasePatSubst (imap : InstMap) (subst : Substitution) (slot : SlotIndex) :
    InstMap :=
  imap.modifyMapsForSlotsFrom slot λ ms hs =>
    let ms := PersistentHashSet.filter (·.containsPatSubst subst) ms
    let hs := hs.erase { fvarId? := none, subst }
    (ms, hs)

end InstMap

set_option linter.missingDocs false in
/-- Map from variables to the matches and hypotheses of slots whose types
contain the variables. -/
structure VariableMap where
  map : PHashMap PremiseIndex InstMap
  deriving Inhabited

namespace VariableMap

instance : EmptyCollection VariableMap :=
  ⟨⟨.empty⟩⟩

instance : ToMessageData VariableMap where
  toMessageData m := ppPHashMap (indent := true) m.map

/-- Get the `InstMap` associated with a variable. -/
def find? (vmap : VariableMap) (var : PremiseIndex) : Option InstMap :=
  vmap.map.find? var

/-- Get the `InstMap` associated with a variable, or an empty `InstMap`. -/
def find (vmap : VariableMap) (var : PremiseIndex) : InstMap :=
  vmap.find? var |>.getD ∅

/-- Modify the `InstMap` associated to variable `var`. If no such `InstMap`
exists, the function `f` is applied to the empty `InstMap` and the result is
associated with `var`. Returns the new variable map and the result of `f`. -/
def modify (vmap : VariableMap) (var : PremiseIndex) (f : InstMap → InstMap × α) :
    VariableMap × α :=
  match vmap.map.find? var with
  | none =>
    let (m, a) := f ∅
    (⟨vmap.map.insert var m⟩, a)
  | some m =>
    let (m, a) := f m
    (⟨vmap.map.insert var m⟩, a)

/-- Add a hypothesis `hyp`. Precondition: `hyp` matches the premise of slot
`slot` with substitution `hyp.subst` (and hence `hyp.subst` contains a mapping
for each variable in `slot.common`). Returns `true` if the variable map
changed. -/
def addHyp (vmap : VariableMap) (slot : Slot) (hyp : Hyp) : VariableMap × Bool :=
  slot.common.fold (init := (vmap, false)) λ (vmap, changed) var =>
    if let some inst := hyp.subst.find? var then
      let (vmap, changed') := vmap.modify var (·.insertHyp slot.index inst hyp)
      (vmap, changed || changed')
    else
      panic! s!"substitution contains no instantiation for variable {var}"

/-- Add a match `m`. Precondition: `nextSlot` is the slot with index
`m.level + 1`. Returns `true` if the variable map changed. -/
def addMatch (vmap : VariableMap) (nextSlot : Slot) (m : Match) :
    VariableMap × Bool :=
  nextSlot.common.fold (init := (vmap, false)) λ (vmap, changed) var =>
    let (vmap, changed') := vmap.modify var (·.insertMatch var m)
    (vmap, changed || changed')

/-- Remove a hyp from `slot` and all later slots. -/
def eraseHyp (vmap : VariableMap) (hyp : FVarId) (slot : SlotIndex) :
    VariableMap :=
  ⟨vmap.map.map (·.eraseHyp hyp slot)⟩

/-- Remove the pattern substitution `subst` from `slot` and all later slots. -/
def erasePatSubst (vmap : VariableMap) (subst : Substitution) (slot : SlotIndex) :
    VariableMap :=
  ⟨vmap.map.map (·.erasePatSubst subst slot)⟩

/-- Find matches in slot `slot - 1` whose substitutions are compatible with
`subst`. Preconditions: `slot.index` is nonzero, `slot.common` is nonempty and
each variable contained in `slot.common` is also contained in `subst`. -/
def findMatches (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    Std.HashSet Match := Id.run do
  if slot.index == ⟨0⟩ then
    panic! "slot has index 0"
  let common := slot.common.toArray
  if h : 0 < common.size then
    let firstVar := common[0]
    let mut ms := prevSlotMatches firstVar |> PersistentHashSet.toHashSet
    for var in common[1:] do
      if ms.isEmpty then
        break
      let ms' := prevSlotMatches var
      ms := ms.filter (ms'.contains ·)
    return ms
  else
    panic! "no common variables"
where
  prevSlotMatches (var : PremiseIndex) : PHashSet Match :=
    if let some inst := subst.find? var then
      vmap.find var |>.findD (slot.index - 1) inst |>.1
    else
      panic! s!"substitution contains no instantiation for variable {var}"

/-- Find hyps in `slot` whose substitutions are compatible with `subst`.
Precondition: `slot.common` is nonempty and each variable contained in it is
also contained in `subst`. -/
def findHyps (vmap : VariableMap) (slot : Slot) (subst : Substitution) :
    Std.HashSet Hyp := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps := slotHyps common[0] |> PersistentHashSet.toHashSet
    for var in common[1:] do
      if hyps.isEmpty then
        break
      let hyps' := slotHyps var
      hyps := hyps.filter (hyps'.contains ·)
    return hyps
  else
    panic! "no common variables"
where
  slotHyps (var : PremiseIndex) : PHashSet Hyp :=
    if let some inst := subst.find? var then
      vmap.find var |>.findD slot.index inst |>.2
    else
      panic! s!"substitution contains no instantiation for variable {var}"

end VariableMap

/-- Structure representing the state of a slot cluster. -/
structure ClusterState where
  /-- The cluster's slots. -/
  slots : Array Slot
  /-- The premises that appear in the rule's conclusion. These are the same for
  all cluster states of a rule, but are stored here for convenience. -/
  conclusionDeps : Array PremiseIndex
  /-- The variable map for this cluster. -/
  variableMap : VariableMap
  /-- Complete matches for this cluster. -/
  completeMatches : PHashSet Match
  /-- When this flag is `true`, hyps are added to the `slotQueues` rather than
  the `variableMap`. This is an optimisation that avoids performing unifications
  until a rule can potentially generate a complete match. More precisely:

  - `addHypsLazily` is initially set to `true`.
  - While `addHypsLazily` is `true`, hyps are added to (and deleted from) the
    `slotQueues` and are not added to the `variableMap`.
    Once an addition causes all slot queues to have at least one element,
    `addHypsLazily` is permanently set to `false` and hyps for slot 0 are added
    to the `variableMap`.
  - While `addHypsLazily` is `false`:
    - Hyps for slot `i` are added directly to the variable maps if `i = 0` or
      the slot `i - 1` has matches. Otherwise they are added to the slot queue
      for `i`. (More precisely, we only track whether slot `i - 1` has had
      matches at some point. This allows us to ignore deletions.)
    - The insertion of a match into slot `i` causes all hyps at slot `i + 1`
      to be moved from the slot queue into the `variableMap`.
  -/
  addHypsLazily : Bool
  /-- Hypotheses or pattern substitutions that have been added to the cluster
  state, but have not yet been added to the `variableMap`. -/
  slotQueues : Array (Array RawHyp)
  /-- There is exactly one queue for each slot. -/
  slotQueues_size : slotQueues.size = slots.size
  /-- The `i`th element of this array is `true` if a match was at some point
  added to slot `i`. -/
  slotMaybeHasMatches : Array Bool
  /-- There is exactly one boolean for each slot. -/
  slotMaybeHasMatches_size : slotMaybeHasMatches.size = slots.size

namespace ClusterState

instance : Inhabited ClusterState where
  default := by refine' {
    slots := #[]
    slotQueues := #[]
    slotQueues_size := by simp
    slotMaybeHasMatches := #[]
    slotMaybeHasMatches_size := by simp
    ..
  } <;> exact default

instance : ToMessageData ClusterState where
  toMessageData cs :=
    m!"variables:{indentD $ toMessageData cs.variableMap}\n\
       complete matches:{indentD $ .joinSep (PersistentHashSet.toList cs.completeMatches |>.map toMessageData) "\n"}"

/-- Get the slot with the given index. Panic if the index is invalid. -/
@[macro_inline, always_inline]
def slot! (cs : ClusterState) (slot : SlotIndex) : Slot :=
  cs.slots[slot.toNat]!

/-- Get the slot with the given premise index. -/
def findSlot? (cs : ClusterState) (i : PremiseIndex) : Option Slot :=
  cs.slots.find? (·.premiseIndex == i)

/-- Match hypothesis `hyp` against the slot with index `slot` in `cs` (which
must be a valid index). -/
def matchPremise? (premises : Array MVarId) (lmvarIds : Array LMVarId)
    (cs : ClusterState) (slot : SlotIndex) (hyp : FVarId) :
    BaseM (Option Substitution) := do
  let some slot := cs.slots[slot.toNat]?
    | throwError "aesop: internal error: matchPremise?: no slot with index {slot}"
  let premiseIdx := slot.premiseIndex.toNat
  let some slotPremise := premises[premiseIdx]?
    | throwError "aesop: internal error: matchPremise?: slot with premise index {premiseIdx}, but only {premises.size} premises"
  let premiseType ← slotPremise.getType
  let hypType ← hyp.getType
  withAesopTraceNodeBefore .forward (return m!"match against premise {premiseIdx}: {hypType} ≟ {premiseType}") do
  withoutModifyingState do
    let isDefEq ←
      withConstAesopTraceNode .forwardDebug (return m!"defeq check") do
      withReducible do
        isDefEq premiseType hypType
    if isDefEq then
      let mut subst := .empty premises.size lmvarIds.size
      for var in slot.deps do
        subst ← updateSubst premises var subst
      subst := subst.insert slot.premiseIndex $ ← rpinf (.fvar hyp)
      for h : i in [:lmvarIds.size] do
        if let some l ← getLevelMVarAssignment? lmvarIds[i] then
          subst := subst.insertLevel ⟨i⟩ (← instantiateLevelMVars l)
      aesop_trace[forward] "substitution: {subst}"
      return subst
    else
      return none
where
  updateSubst (premises : Array MVarId) (var : PremiseIndex)
      (subst : Substitution) : BaseM Substitution :=
    withConstAesopTraceNode .forwardDebug (return m!"update var {var}") do
      let some varMVarId := premises[var.toNat]?
        | throwError "aesop: internal error: matchPremise?: dependency with index {var}, but only {premises.size} premises"
      let mvar := .mvar varMVarId
      let assignment ← instantiateMVars mvar
      if assignment == mvar then
        throwError "aesop: internal error: matchPremise?: while matching hyp {hyp.name}: no assignment for variable {var}"
      if ← hasAssignableMVar assignment then
        throwError "aesop: internal error: matchPremise?: assignment has mvar:{indentExpr assignment}"
      let assignment ← rpinf assignment
      return subst.insert var assignment

/-- Context for the `AddM` monad. -/
structure AddM.Context where
  /-- Metavariables for the premises of the rule for which a hyp or match is
  being added. When adding hyps, they are unified with these metavariables. -/
  premiseMVars : Array MVarId
  /-- Metavariables for level parameters appearing in the rule's premises. -/
  premiseLMVars : Array LMVarId

/-- A monad for operations that add hyps or matches to a cluster state. The
monad's state is an array of complete matches discovered while adding
hyps/matches. -/
abbrev AddM := ReaderT AddM.Context $ StateRefT (Array Match) $ BaseM

/-- Run an `AddM` action. -/
def AddM.run (premiseMVars : Array MVarId) (premiseLMVars : Array LMVarId)
    (x : AddM α) : BaseM (α × Array Match) :=
  ReaderT.run x { premiseMVars, premiseLMVars } |>.run #[]

mutual
  /-- Add a match to the cluster state. Returns the new cluster state and any new
  complete matches for this cluster. -/
  partial def addMatch (cs : ClusterState) (m : Match) : AddM ClusterState := do
    let mut cs := cs
    let slotIdx := m.level
    if slotIdx.toNat == cs.slots.size - 1 then
      if cs.completeMatches.contains m then
        aesop_trace[forward] "complete match {m} already present"
        return cs
      else
        cs := { cs with completeMatches := cs.completeMatches.insert m }
        modify (·.push m)
        return cs
    else
      let nextSlot := cs.slot! $ slotIdx + 1
      aesop_trace[forward] "add match {m} for slot {slotIdx}"
      let (vmap, changed) := cs.variableMap.addMatch nextSlot m  -- This is correct; VariableMap.addMatch needs the next slot.
      if ! changed then
        aesop_trace[forward] "match already present"
        return cs
      cs := {
        cs with
        variableMap := vmap
        slotMaybeHasMatches := cs.slotMaybeHasMatches.set! slotIdx.toNat true
        slotMaybeHasMatches_size := by simp [cs.slotMaybeHasMatches_size]
      }
      cs ← cs.addQueuedRawHyps nextSlot
      for hyp in cs.variableMap.findHyps nextSlot m.subst do
        let m := m.addHypOrPatSubst hyp.subst hyp.isPatSubst nextSlot.forwardDeps
        cs ← cs.addMatch m
      return cs

  /-- Add a hypothesis to the cluster state. `hyp.subst` must be the substitution
  that results from applying `h` to `slot`. -/
  partial def addHyp (cs : ClusterState) (slot : Slot) (h : Hyp) :
      AddM ClusterState := do
    withConstAesopTraceNode .forward (return m!"add hyp or pattern inst for slot {slot.index} with substitution {h.subst}") do
    if slot.index.toNat == 0 then
      let m :=
        Match.initial h.subst h.isPatSubst (forwardDeps := slot.forwardDeps)
          (conclusionDeps := cs.conclusionDeps)
      cs.addMatch m
    else
      let (vmap, changed) := cs.variableMap.addHyp slot h
      if ! changed then
        aesop_trace[forward] "hyp already present"
        return cs
      let mut cs := { cs with variableMap := vmap }
      for pm in cs.variableMap.findMatches slot h.subst do
        let m := pm.addHypOrPatSubst h.subst h.isPatSubst slot.forwardDeps
        cs ← cs.addMatch m
      return cs

  /-- Add a hypothesis or pattern substitution to the cluster state. -/
  partial def addRawHypCore (h : RawHyp) (slot : Slot) (cs : ClusterState) :
      AddM ClusterState :=
    match h with
    | .fvarId fvarId =>
      withConstAesopTraceNode .forwardDebug (return m!"add hyp {Expr.fvar fvarId} ({fvarId.name}) to slot {slot.index}") do
        let some subst ←
          cs.matchPremise? (← read).premiseMVars (← read).premiseLMVars
            slot.index fvarId
          | return cs
        cs.addHyp slot { fvarId? := fvarId, subst }
    | .patSubst subst =>
      withConstAesopTraceNode .forwardDebug (return m!"add pattern subst {subst} to slot {slot.index}") do
        cs.addHyp slot { fvarId? := none, subst }

  /-- Insert the raw hyps from `slot`'s queue into the variable map. -/
  partial def addQueuedRawHyps (slot : Slot) (cs : ClusterState) :
      AddM ClusterState :=
    withConstAesopTraceNode .forward (return m!"add queued hyps for slot {slot.index}") do
      let cs ← cs.slotQueues[slot.index.toNat]!.foldlM (init := cs) λ cs h =>
        cs.addRawHypCore h slot
      return {
        cs with
        slotQueues := cs.slotQueues.set! slot.index.toNat #[]
        slotQueues_size := by simp [cs.slotQueues_size]
      }
end

/-- Add a hypothesis or pattern substitution to the queue for its slot. If
afterwards each slot queue contains at least one element, then the returned
cluster state `cs` has `cs.addHypsLazily = false`. -/
def enqueueRawHyp (h : RawHyp) (slot : Slot) (cs : ClusterState) :
    ClusterState := Id.run do
  let mut cs := {
    cs with
    slotQueues := cs.slotQueues.modify slot.index.toNat (·.push h)
    slotQueues_size := by simp [cs.slotQueues_size]
  }
  if cs.slotQueues.all (·.size > 0) then
    cs := { cs with addHypsLazily := false }
  return cs

/-- Add a hypothesis or pattern substitution to the cluster state. If a
hypothesis is given and its type does not match the premise corresponding to
`slot`, it is not added. -/
def addRawHyp (cs : ClusterState) (i : PremiseIndex) (h : RawHyp) :
    AddM ClusterState := do
  let some slot := cs.findSlot? i
    | return cs
  if cs.addHypsLazily then
    let cs := cs.enqueueRawHyp h slot
    if ! cs.addHypsLazily then
      cs.addQueuedRawHyps (cs.slot! ⟨0⟩)
    else
      return cs
  else if slot.index.toNat == 0 || cs.slotMaybeHasMatches[slot.index.toNat - 1]! then
    cs.addRawHypCore h slot
  else
    return cs.enqueueRawHyp h slot

/-- Erase a `RawHyp` from the slot queue of the given slot. -/
def eraseEnqueuedRawHyp (h : RawHyp) (slot : Slot) (cs : ClusterState) :
    ClusterState := {
  cs with
  slotQueues := cs.slotQueues.modify slot.index.toNat λ q => q.erase h
  slotQueues_size := by simp [cs.slotQueues_size]
}

private def filterPHashSet [BEq α] [Hashable α] (p : α → Bool)
    (s : PHashSet α) : PHashSet α :=
  let toDelete := s.fold (init := #[]) λ toDelete a =>
    if p a then toDelete else toDelete.push a
  toDelete.foldl (init := s) λ s a => s.erase a

/-- Erase a hypothesis from the cluster state's variable map. -/
def eraseHyp (h : FVarId) (pi : PremiseIndex) (cs : ClusterState) :
    ClusterState := Id.run do
  let some slot := cs.findSlot? pi
    | return cs
  if cs.addHypsLazily then
    return cs.eraseEnqueuedRawHyp (.fvarId h) slot
  else
    return {
      cs with
      variableMap := cs.variableMap.eraseHyp h slot.index
      completeMatches := filterPHashSet (! ·.containsHyp h) cs.completeMatches
      -- TODO inefficient: complete matches should only be filtered once
    }

/-- Erase a pattern substitution from the cluster state. -/
def erasePatSubst (subst : Substitution) (pi : PremiseIndex) (cs : ClusterState) :
    ClusterState := Id.run do
  let some slot := cs.findSlot? pi
    | return cs
  if cs.addHypsLazily then
    return cs.eraseEnqueuedRawHyp (.patSubst subst) slot
  else
    return {
      cs with
      variableMap := cs.variableMap.erasePatSubst subst slot.index
      completeMatches := filterPHashSet (! ·.containsPatSubst subst) cs.completeMatches
    }

end ClusterState

/-- The source of a pattern substitution. The same substitution can have
multiple sources. -/
inductive PatSubstSource
  /-- The pattern substitution came from the given hypothesis. -/
  | hyp (fvarId : FVarId)
  /-- The pattern substitution came from the goal's target. -/
  | target
  deriving Inhabited, Hashable, BEq

/-- Forward state for one rule. -/
structure RuleState where
  /-- The rule to which this state belongs. -/
  rule : ForwardRule
  /-- States for each of the rule's slot clusters. -/
  clusterStates : Array ClusterState
  /-- The sources of all pattern substitutions present in the
  `clusterStates`. Invariant: each pattern substitution in the cluster states
  is associated with a nonempty set. -/
  patSubstSources : PHashMap Substitution (PHashSet PatSubstSource)
  deriving Inhabited

instance : ToMessageData RuleState where
  toMessageData rs :=
    flip MessageData.joinSep "\n" $
      rs.clusterStates.toList.mapIdx λ i cs =>
        m!"cluster {i}:{indentD $ toMessageData cs}"

/-- The initial (empty) rule state for a given forward rule. -/
def ForwardRule.initialRuleState (r : ForwardRule) : RuleState :=
  let clusterStates := r.slotClusters.map λ slots => {
    variableMap := ∅
    completeMatches := {}
    conclusionDeps := r.conclusionDeps
    slotQueues := .replicate slots.size #[]
    slotQueues_size := by simp
    slotMaybeHasMatches := .replicate slots.size false
    slotMaybeHasMatches_size := by simp
    addHypsLazily := true
    slots
  }
  { rule := r, clusterStates, patSubstSources := {} }

namespace RuleState

/-- Add a hypothesis or pattern substitution to the rule state. Returns the new
rule state and any newly completed matches. If a hypothesis is given and it does
not match premise `pi`, nothing happens. -/
def addRawHyp (goal : MVarId) (h : RawHyp) (pi : PremiseIndex) (rs : RuleState) :
    BaseM (RuleState × Array CompleteMatch) :=
  withNewMCtxDepth do
    -- TODO We currently open the rule expression also if `h` is a pattern
    -- substitution, which is unnecessary.
    let some ruleExpr ←
      withConstAesopTraceNode .forwardDebug (return m!"elab rule term") do
        show MetaM _ from observing? $ elabForwardRuleTerm goal rs.rule.term
      | return (rs, #[])
    let lmvars := collectLevelMVars {} ruleExpr |>.result
    if lmvars.size != rs.rule.numLevelParams then
      aesop_trace[forward] "failed to add hyp or pat inst: rule term{indentD $ toMessageData rs.rule.term}\ndoes not have expected number of level mvars {rs.rule.numLevelParams}"
      return (rs, #[])
    let ruleType ← instantiateMVars (← inferType ruleExpr)
    let (premises, _, _) ←
      withConstAesopTraceNode .forwardDebug (return m!"open rule term") do
      withReducible do
        forallMetaTelescope ruleType
    if premises.size != rs.rule.numPremises then
      aesop_trace[forward] "failed to add hyp or pat inst: rule term{indentD $ toMessageData rs.rule.term}\ndoes not have expected number of premises {rs.rule.numPremises}"
      return (rs, #[])
    let premises := premises.map (·.mvarId!)
    let mut rs := rs
    let mut clusterStates := rs.clusterStates
    let mut completeMatches := #[]
    for i in [:clusterStates.size] do
      let cs := clusterStates[i]!
      let (cs, newCompleteMatches) ← cs.addRawHyp pi h |>.run premises lmvars
      clusterStates := clusterStates.set! i cs
      completeMatches ←
        withConstAesopTraceNode .forwardDebug (return m!"construct new complete matches") do
          return completeMatches ++
                 getCompleteMatches clusterStates i newCompleteMatches
    return ({ rs with clusterStates }, completeMatches)
where
  getCompleteMatches (clusterStates : Array ClusterState) (clusterIdx : Nat)
      (newCompleteMatches : Array Match) :
      Array CompleteMatch := Id.run do
    if newCompleteMatches.isEmpty ||
       clusterStates.any (·.completeMatches.isEmpty) then
      return #[]
    else
      let mut completeMatches := #[]
      for h : i in [:clusterStates.size] do
        completeMatches :=
          if i == clusterIdx then
            addMatches completeMatches newCompleteMatches
          else
            addMatches completeMatches $
              PersistentHashSet.toArray clusterStates[i].completeMatches
      return completeMatches

  addMatches (completeMatches : Array CompleteMatch)
      (clusterMatches : Array Match) : Array CompleteMatch := Id.run do
    if completeMatches.isEmpty then
      return clusterMatches.map ({ clusterMatches := #[·] })
    else
      let mut newCompleteMatches :=
        Array.mkEmpty (completeMatches.size * clusterMatches.size)
      for completeMatch in completeMatches do
        for clusterMatch in clusterMatches do
          newCompleteMatches := newCompleteMatches.push
            { clusterMatches := completeMatch.clusterMatches.push clusterMatch }
      return newCompleteMatches

/-- Erase a pattern substitution that was obtained from the given source. -/
def erasePatSubst (subst : Substitution) (source : PatSubstSource)
    (rs : RuleState) : RuleState := Id.run do
  let some sources := rs.patSubstSources[subst]
    | panic! s!"unknown pattern substitution {subst.premises} for rule {rs.rule.name}"
  let sources := sources.erase source
  if sources.isEmpty then
    let some (pat, patPremiseIdx) := rs.rule.rulePatternInfo?
      | panic! s!"rule {rs.rule.name} does not have a pattern"
    let some csIdx := rs.clusterStates.findIdx? λ cs =>
      cs.findSlot? patPremiseIdx |>.isSome
      | panic! s!"pattern slot {patPremiseIdx} not found for rule {rs.rule.name}"
    return {
      rs with
      clusterStates := rs.clusterStates.modify csIdx λ cs =>
        cs.erasePatSubst subst patPremiseIdx
      patSubstSources := rs.patSubstSources.erase subst
    }
  else
    return { rs with patSubstSources := rs.patSubstSources.insert subst sources }

/-- Erase a hypothesis from the rule state. -/
def eraseHyp (h : FVarId) (pi : PremiseIndex) (rs : RuleState) : RuleState :=
  let clusterStates := rs.clusterStates.map (·.eraseHyp h pi)
  { rs with clusterStates }

end RuleState

/-- State representing the non-complete matches of a given set of forward rules
in a given local context. -/
structure ForwardState where
  /-- Map from each rule's name to its `RuleState`-/
  ruleStates : PHashMap RuleName RuleState
  /-- A map from hypotheses to the rules and premises that they matched against
  when they were initially added to the rule state. Invariant: the rule states
  in which a hypothesis `h` appear are exactly those identified by the rule
  names in `hyps[h]`. Furthermore, `h` only appears in slots with premise
  indices greater than or equal to those in `hyps[h]`. -/
  hyps : PHashMap FVarId (PArray (RuleName × PremiseIndex))
  /-- The pattern substitutions present in the rule states. Invariant:
  `patSubsts` maps the source `s` to a rule name `r` and pattern substitution `i`
  iff the rule state of `r` contains `i` with source `s`. -/
  patSubsts : PHashMap PatSubstSource (PArray (RuleName × Substitution))
  /-- Normalised types of all non-implementation detail hypotheses in the
  local context. -/
  hypTypes : PHashSet RPINF
 deriving Inhabited

namespace ForwardState

instance : EmptyCollection ForwardState where
  emptyCollection := by refine' {..} <;> exact .empty

instance : ToMessageData ForwardState where
  toMessageData fs :=
    flip MessageData.joinSep "\n" $
      fs.ruleStates.foldl (init := []) λ result r rs =>
        m!"{r}:{indentD $ toMessageData rs}" :: result

private def addForwardRuleMatches (acc : Array ForwardRuleMatch)
    (r : ForwardRule) (completeMatches : Array CompleteMatch) :
    MetaM (Array ForwardRuleMatch) := do
  let ruleMatches :=
    completeMatches.foldl (init := acc) λ ruleMatches «match» =>
      ruleMatches.push { rule := r, «match» }
  aesop_trace[forward] do
    for m in ruleMatches do
      aesop_trace![forward] "new complete match for {m.rule.name}:{indentD $ toMessageData m}"
  return ruleMatches

/-- Add a hypothesis to the forward state. If `fs` represents a local context
`lctx`, then `fs.addHyp h ms` represents `lctx` with `h` added. `ms` must
overapproximate the rules for which `h` may unify with a maximal premise. -/
def addHypCore (ruleMatches : Array ForwardRuleMatch) (goal : MVarId)
    (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) := do
  goal.withContext do
  withConstAesopTraceNode .forward (return m!"add hyp {Expr.fvar h} ({h.name})") do
    let hTypeRPINF ← rpinf (← h.getType)
    if (← isProp hTypeRPINF.toExpr) && fs.hypTypes.contains hTypeRPINF then
      aesop_trace[forward] "a hyp with the same (propositional) type was already added"
      return (fs,ruleMatches)
    let fs := { fs with hypTypes := fs.hypTypes.insert hTypeRPINF }
    ms.foldlM (init := (fs, ruleMatches)) λ (fs, ruleMatches) (r, i) => do
      withConstAesopTraceNode .forward (return m!"rule {r.name}, premise {i}") do
        let rs := fs.ruleStates.find? r.name |>.getD r.initialRuleState
        let (rs, newRuleMatches) ← rs.addRawHyp goal (.fvarId h) i
        let ruleStates := fs.ruleStates.insert r.name rs
        let hyps := fs.hyps.insert h $
          ms.map (λ (r, i) => (r.name, i)) |>.toPArray'
        let fs := { fs with ruleStates, hyps }
        let ms ← addForwardRuleMatches ruleMatches r newRuleMatches
        return (fs, ms)

@[inherit_doc addHypCore]
def addHyp (goal : MVarId) (h : FVarId)
    (ms : Array (ForwardRule × PremiseIndex)) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  fs.addHypCore #[] goal h ms

/-- Add a pattern substitution to the forward state. -/
def addPatSubstCore (ruleMatches : Array ForwardRuleMatch) (goal : MVarId)
    (r : ForwardRule) (patSubst : Substitution) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
  withConstAesopTraceNode .forward (return m!"add pat inst {patSubst} to rule {r.name}") do
    let rs := fs.ruleStates.find? r.name |>.getD r.initialRuleState
    let some (_, patSlotPremiseIdx) := r.rulePatternInfo?
      | throwError "aesop: internal error: addPatSubstCore: rule {r.name} does not have a rule pattern"
    let (rs, newRuleMatches) ←
      rs.addRawHyp goal (.patSubst patSubst) patSlotPremiseIdx
    let fs := { fs with ruleStates := fs.ruleStates.insert r.name rs }
    let ms ← addForwardRuleMatches ruleMatches r newRuleMatches
    return (fs, ms)

@[inherit_doc addPatSubstCore]
def addPatSubst (goal : MVarId) (r : ForwardRule) (patSubst : Substitution)
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) :=
  fs.addPatSubstCore #[] goal r patSubst

/-- Add multiple pattern substitutions to the forward state. -/
def addPatSubstsCore (ruleMatches : Array ForwardRuleMatch) (goal : MVarId)
    (patSubsts : Array (ForwardRule × Substitution)) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) := do
  patSubsts.foldlM (init := (fs, ruleMatches))
    λ (fs, ruleMatches) (r, patSubst) =>
      fs.addPatSubstCore ruleMatches goal r patSubst

@[inherit_doc addPatSubstsCore]
def addPatSubsts (goal : MVarId) (patSubsts : Array (ForwardRule × Substitution))
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) :=
  fs.addPatSubstsCore #[] goal patSubsts

/-- Add a hypothesis and to the forward state, along with any rule pattern
substitutions obtained from it. -/
def addHypWithPatSubstsCore (ruleMatches : Array ForwardRuleMatch) (goal : MVarId)
    (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (patSubsts : Array (ForwardRule × Substitution)) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) := do
  let (fs, ruleMatches) ← fs.addHypCore ruleMatches goal h ms
  fs.addPatSubstsCore ruleMatches goal patSubsts

@[inherit_doc addHypWithPatSubstsCore]
def addHypWithPatSubsts (goal : MVarId) (h : FVarId)
    (ms : Array (ForwardRule × PremiseIndex))
    (patSubsts : Array (ForwardRule × Substitution)) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  fs.addHypWithPatSubstsCore #[] goal h ms patSubsts

/-- Erase pattern substitutions with the given source. -/
def erasePatSubsts (source : PatSubstSource) (fs : ForwardState) :
    ForwardState := Id.run do
  let mut ruleStates := fs.ruleStates
  for (r, inst) in fs.patSubsts[source].getD {} do
    let some rs := ruleStates.find? r
      | panic! s!"patSubsts entry for rule {r}, but no rule state"
    let rs := rs.erasePatSubst inst source
    ruleStates := ruleStates.insert r rs
  return { fs with patSubsts := fs.patSubsts.erase source, ruleStates }

/-- Remove a hypothesis from the forward state. If `fs` represents a local
context `lctx`, then `fs.eraseHyp h ms` represents `lctx` with `h` removed.
`type` must be the normalised type of `h`. `ms` must contain all rules for which
`h` may unify with a maximal premise. -/
def eraseHyp (h : FVarId) (type : RPINF) (fs : ForwardState) :
    ForwardState := Id.run do
  let mut ruleStates := fs.ruleStates
  for (r, i) in fs.hyps[h].getD {} do
    let some rs := ruleStates.find? r
      | panic! s!"hyps entry for rule {r}, but no rule state"
    let rs := rs.eraseHyp h i
    ruleStates := ruleStates.insert r rs
  let fs := {
    fs with
    hyps := fs.hyps.erase h, ruleStates
    hypTypes := fs.hypTypes.erase type
  }
  fs.erasePatSubsts (.hyp h)

/-- Erase all pattern substitutions whose source is the target. -/
def eraseTargetPatSubsts (fs : ForwardState) : ForwardState :=
  fs.erasePatSubsts .target

/-- Update the pattern substitutions after the goal's target changed.
`goal` is the new goal. `newPatSubsts` are the new target's pattern
substitutions. -/
def updateTargetPatSubstsCore (ruleMatches : Array ForwardRuleMatch)
    (goal : MVarId)
    (newPatSubsts : Array (ForwardRule × Substitution)) (fs : ForwardState) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  -- TODO Instead of erasing all target pattern substitutions, erase only those
  -- not present in the new target.
  let fs := fs.eraseTargetPatSubsts
  fs.addPatSubstsCore ruleMatches goal newPatSubsts

@[inherit_doc updateTargetPatSubstsCore]
def updateTargetPatSubsts (goal : MVarId)
    (newPatSubsts : Array (ForwardRule × Substitution))
    (fs : ForwardState) : BaseM (ForwardState × Array ForwardRuleMatch) :=
  fs.updateTargetPatSubstsCore #[] goal newPatSubsts

end Aesop.ForwardState
