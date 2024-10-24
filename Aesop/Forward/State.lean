/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.Match
import Aesop.Index.Forward

open Lean Lean.Meta
open ExceptToEmoji (toEmoji)

set_option linter.missingDocs true

namespace Aesop

variable [Monad M] [MonadTrace M] [MonadOptions M] [MonadRef M]
  [AddMessageContext M] [MonadLiftT IO M]

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

/-- A hypothesis that was matched against a premise. -/
structure Hyp where
  /-- The hypothesis. -/
  fvarId : FVarId
  /-- The substitution that results from matching `fvarId` against a premise. -/
  subst : Substitution
  deriving Inhabited

instance : BEq Hyp where
  beq h₁ h₂ := h₁.fvarId == h₂.fvarId

instance : Hashable Hyp where
  hash h := hash h.fvarId

set_option linter.missingDocs false in
/-- Partial matches associated with a particular slot instantiation. An entry
`s ↦ e ↦ (ms, hs)` indicates that for the instantiation `e` of slot `s`, we have
partial matches `ms` and hypotheses `hs`. -/
structure InstMap where
  map : PHashMap SlotIndex (PHashMap Expr (PHashSet Match × PHashSet Hyp))
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
                hs.push (Expr.fvar h.fvarId)
            (ppPHashSet ms, hs)

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`. -/
@[inline]
def find? (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    Option (PHashSet Match × PHashSet Hyp) :=
  imap.map.find? slot |>.bind λ slotMap => slotMap.find? inst

/-- Returns the set of matches and hypotheses associated with a slot `slot`
with instantiation `inst`, or `(∅, ∅)` if `slot` and `inst` do not have any
associated matches. -/
@[inline]
def findD (imap : InstMap) (slot : SlotIndex) (inst : Expr) :
    PHashSet Match × PHashSet Hyp :=
  imap.find? slot inst |>.getD (∅, ∅)

/-- Applies a transfomation to the data associated to `slot` and `inst`.
If the there is no such data, the transformation is applied to `(∅, ∅)`. -/
def modify (imap : InstMap) (slot : SlotIndex) (inst : Expr)
    (f : PHashSet Match → PHashSet Hyp → PHashSet Match × PHashSet Hyp) :
    InstMap :=
  let (ms, hyps) := imap.findD slot inst
  let slotMap := imap.map.findD slot .empty |>.insert inst (f ms hyps)
  ⟨imap.map.insert slot slotMap⟩

/-- Inserts a hyp associated with slot `slot` and instantiation `inst`.
The hyp should be a valid assignment for the slot's premise. -/
def insertHyp (imap : InstMap) (slot : SlotIndex) (inst : Expr) (hyp : Hyp) :
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
def insertMatch (imap : InstMap) (var : PremiseIndex) (m : Match) :
    InstMap := Id.run do
  let some inst := m.subst.find? var
    | panic! s!"variable {var} is not assigned in substitution"
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
      m.insert e (ms, hs.erase { fvarId := hyp, subst := default })
    imaps := imaps.insert i maps
  return { map := imaps }

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
associated with `var`. -/
def modify (vmap : VariableMap) (var : PremiseIndex) (f : InstMap → InstMap) :
    VariableMap :=
  match vmap.map.find? var with
  | none => ⟨vmap.map.insert var (f ∅)⟩
  | some m => ⟨vmap.map.insert var (f m)⟩

/-- Add a hypothesis `hyp`. Precondition: `hyp` matches the premise of slot
`slot` with substitution `hyp.subst` (and hence `hyp.subst` contains a mapping
for each variable in `slot.common`). -/
def addHyp (vmap : VariableMap) (slot : Slot) (hyp : Hyp) : VariableMap :=
  slot.common.fold (init := vmap) λ vmap var =>
    if let some inst := hyp.subst.find? var then
      vmap.modify var (·.insertHyp slot.index inst hyp)
    else
      panic! s!"substitution contains no instantiation for variable {var}"

/-- Add a match `m`. Precondition: `nextSlot` is the slot with index
`m.level + 1`. -/
def addMatch (vmap : VariableMap) (nextSlot : Slot) (m : Match) : VariableMap :=
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
  /-- The variable map for this cluster. -/
  variableMap : VariableMap
  /-- Complete matches for this cluster. -/
  completeMatches : PArray Match
  deriving Inhabited

namespace ClusterState

instance : ToMessageData ClusterState where
  toMessageData cs :=
    m!"variables:{indentD $ toMessageData cs.variableMap}\n\
       complete matches:{indentD $ .joinSep (cs.completeMatches.toList.map toMessageData) "\n"}"

/-- Get the slot with the given index. Panic if the index is invalid. -/
@[macro_inline, always_inline]
def slot! (cs : ClusterState) (slot : SlotIndex) : Slot :=
  cs.slots[slot.toNat]!

/-- Get the slot with the given premise index. -/
def findSlot? (cs : ClusterState) (i : PremiseIndex) : Option Slot :=
  cs.slots.find? (·.premiseIndex == i)

/-- Match hypothesis `hyp` against the slot with index `slot` in `cs` (which
must be a valid index). -/
def matchPremise? (premises : Array MVarId) (cs : ClusterState)
    (slot : SlotIndex) (hyp : FVarId) : MetaM (Option Substitution) := do
  let some slot := cs.slots[slot.toNat]?
    | throwError "aesop: internal error: matchPremise?: no slot with index {slot}"
  let some slotPremise := premises[slot.premiseIndex.toNat]?
    | throwError "aesop: internal error: matchPremise?: slot with premise index {slot.premiseIndex}, but only {premises.size} premises"
  let inputHypType ← slotPremise.getType
  let hypType ← hyp.getType
  withAesopTraceNodeBefore .forward (return m!"match against premise {slot.premiseIndex}: {hypType} ≟ {inputHypType}") do
    if ← isDefEq inputHypType hypType then
      /- Note: This was over `slot.common` and not `slot.deps`. We need `slot.deps`
      because, among other issues, `slot.common` is empty in the first slot. Even though
      we don't have dependencies, we still need to keep track of the subs of hyp.
      Otherwise, we would trigger the first panic in `AddHypothesis`.-/
      let mut subst : Substitution := .empty premises.size
      for var in slot.deps do
        let some varMVarId := premises[var.toNat]?
          | throwError "aesop: internal error: matchPremise?: dependency with index {var}, but only {premises.size} premises"
        let mvar := .mvar varMVarId
        let assignment ← instantiateMVars mvar
        if assignment == mvar then
          throwError "aesop: internal error: matchPremise?: while matching hyp {hyp.name}: no assignment for variable {var}"
        if ← hasAssignableMVar assignment then
          throwError "aesop: internal error: matchPremise?: assignment has mvar:{indentExpr assignment}"
        subst := subst.insert var assignment
      aesop_trace[forward] "substitution: {subst}"
      return subst
    else
      return none

/-- Add a match to the cluster state. Returns the new cluster state and any new
complete matches for this cluster. -/
partial def addMatchCore (newCompleteMatches : Array Match) (cs : ClusterState)
    (m : Match) : M (ClusterState × Array Match) := do
  let mut cs := cs
  let slotIdx := m.level
  if slotIdx.toNat == cs.slots.size - 1 then
    cs := { cs with completeMatches := cs.completeMatches.push m }
    return (cs, newCompleteMatches.push m)
  else
    let nextSlot := cs.slot! $ slotIdx + 1
    aesop_trace[forward] "add match {m.revHyps.reverse.map Expr.fvar} for slot {slotIdx} with subst {m.subst}"
    cs := { cs with variableMap := cs.variableMap.addMatch nextSlot m } -- This is correct; VariableMap.addMatch needs the next slot.
    let mut newCompleteMatches := newCompleteMatches
    for hyp in cs.variableMap.findHyps nextSlot m.subst do
      let m := {
        revHyps := hyp.fvarId :: m.revHyps
        subst := m.subst.mergeCompatible hyp.subst
      }
      let (cs', newCompleteMatches') ← cs.addMatchCore newCompleteMatches m
      cs := cs'
      newCompleteMatches := newCompleteMatches'
    return (cs, newCompleteMatches)

@[inherit_doc addMatchCore]
def addMatch (cs : ClusterState) (m : Match) : M (ClusterState × Array Match) :=
  addMatchCore #[] cs m

/-- Add a hypothesis to the cluster state. `hyp.subst` must be the substitution
that results from applying `h` to `slot`. -/
def addHypCore (newCompleteMatches : Array Match) (cs : ClusterState)
    (slot : Slot) (h : Hyp) : M (ClusterState × Array Match) := do
  aesop_trace[forward] "add hyp {Expr.fvar h.fvarId} for slot {slot.index} with substitution {h.subst}"
  let mut cs :=
    { cs with variableMap := cs.variableMap.addHyp slot h }
  if slot.index.toNat == 0 then
    let m := { revHyps := [h.fvarId], subst := h.subst }
    cs.addMatchCore newCompleteMatches m
  else
    let mut newCompleteMatches := newCompleteMatches
    for pm in cs.variableMap.findMatches slot h.subst do
      let m := {
        revHyps := h.fvarId :: pm.revHyps
        subst := h.subst.mergeCompatible pm.subst
      }
      let (cs', newCompleteMatches') ← cs.addMatchCore newCompleteMatches m
      cs := cs'
      newCompleteMatches := newCompleteMatches'
    return (cs, newCompleteMatches)

/-- Add a hypothesis to the rule state. If the hypothesis's type does not match
the premise corresponding to `slot`, then the hypothesis is not added. -/
def addHyp (premises : Array MVarId) (cs : ClusterState) (i : PremiseIndex)
    (h : FVarId) : MetaM (ClusterState × Array Match) := do
  let some slot := cs.findSlot? i
    | return (cs, #[])
  let some subst ← cs.matchPremise? premises slot.index h
    | return (cs, #[])
  addHypCore #[] cs slot { fvarId := h, subst }

/-- Erase a hypothesis from the cluster state. -/
def eraseHyp (h : FVarId) (pi : PremiseIndex) (cs : ClusterState) :
    ClusterState := Id.run do
  let some slot := cs.findSlot? pi
    | return cs
  { cs with variableMap := cs.variableMap.eraseHyp h slot.index }

end ClusterState

/-- Forward state for one rule. -/
structure RuleState where
  /-- The rule to which this state belongs. -/
  rule : ForwardRule
  /-- States for each of the rule's slot clusters. -/
  clusterStates : Array ClusterState
  deriving Inhabited

instance : ToMessageData RuleState where
  toMessageData rs :=
    flip MessageData.joinSep "\n" $
      rs.clusterStates.toList.mapIdx λ i cs =>
        m!"cluster {i}:{indentD $ toMessageData cs}"

/-- The initial (empty) rule state for a given forward rule. -/
def ForwardRule.initialRuleState (r : ForwardRule) : RuleState :=
  let clusterStates := r.slotClusters.map λ slots =>
    { slots, variableMap := ∅, completeMatches := {} }
  { rule := r, clusterStates }

namespace RuleState

/-- Add a hypothesis to the rule state. Returns the new rule state and any newly
completed matches. If `h` does not match premise `pi`, nothing happens. -/
def addHyp (goal : MVarId) (h : FVarId) (pi : PremiseIndex) (rs : RuleState) :
    MetaM (RuleState × Array CompleteMatch) :=
  withNewMCtxDepth do
    let some ruleExpr ← observing? $ elabForwardRuleTerm goal rs.rule.term
      | return (rs, #[])
    let (premises, _, _) ← forallMetaTelescope (← inferType ruleExpr)
    let premises := premises.map (·.mvarId!)
    let mut rs := rs
    let mut clusterStates := rs.clusterStates
    let mut completeMatches := #[]
    for i in [:clusterStates.size] do
      let cs := clusterStates[i]!
      let (cs, newCompleteMatches) ← cs.addHyp premises pi h
      clusterStates := clusterStates.set! i cs
      completeMatches :=
        completeMatches ++
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
            addMatches completeMatches clusterStates[i].completeMatches.toArray
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

/-- Erase a hypothesis from the rule state. -/
def eraseHyp (h : FVarId) (pi : PremiseIndex) (rs : RuleState) :
    RuleState := Id.run do
  let clusterStates ← rs.clusterStates.mapM λ cs =>
     cs.eraseHyp h pi
  return { rs with clusterStates }

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
 deriving Inhabited

namespace ForwardState

instance : EmptyCollection ForwardState where
  emptyCollection := by refine' {..} <;> exact .empty

instance : ToMessageData ForwardState where
  toMessageData fs :=
    flip MessageData.joinSep "\n" $
      fs.ruleStates.foldl (init := []) λ result r rs =>
        m!"{r}:{indentD $ toMessageData rs}" :: result

/-- Add a hypothesis to the forward state. If `fs` represents a local context
`lctx`, then `fs.addHyp h ms` represents `lctx` with `h` added. `ms` must
overapproximate the rules for which `h` may unify with a maximal premise. -/
def addHypCore (ruleMatches : Array ForwardRuleMatch) (goal : MVarId)
    (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : MetaM (ForwardState × Array ForwardRuleMatch) := do
  goal.withContext do
  withConstAesopTraceNode .forward (return m!"add hyp {Expr.fvar h}") do
    ms.foldlM (init := (fs, ruleMatches)) λ (fs, ruleMatches) (r, i) => do
      withConstAesopTraceNode .forward (return m!"rule {r.name}, premise {i}") do
        let rs := fs.ruleStates.find? r.name |>.getD r.initialRuleState
        let (rs, newRuleMatches) ← rs.addHyp goal h i
        let ruleStates := fs.ruleStates.insert r.name rs
        let hyps := fs.hyps.insert h $
          ms.map (λ (r, i) => (r.name, i)) |>.toPArray'
        let fs := { fs with ruleStates, hyps }
        let ruleMatches :=
          newRuleMatches.foldl (init := ruleMatches) λ ruleMatches «match» =>
            ruleMatches.push { rule := r, «match» }
        aesop_trace[forward] do
          for m in ruleMatches do
            aesop_trace![forward] "new complete match for {m.rule.name}: {m.match.reconstructArgs m.rule}"
        return (fs, ruleMatches)

@[inherit_doc addHypCore]
def addHyp (goal : MVarId) (h : FVarId)
    (ms : Array (ForwardRule × PremiseIndex)) (fs : ForwardState) :
    MetaM (ForwardState × Array ForwardRuleMatch) :=
  fs.addHypCore #[] goal h ms

/-- Remove a hypothesis from the forward state. If `fs` represents a local
context `lctx`, then `fs.eraseHyp h ms` represents `lctx` with `h` removed. `ms`
must contain all rules for which `h` may unify with a maximal premise. -/
def eraseHyp (h : FVarId) (fs : ForwardState) : ForwardState := Id.run do
  let mut ruleStates := fs.ruleStates
  for (r, i) in fs.hyps[h].getD {} do
    let some rs := ruleStates.find? r
      | panic! s!"hyps entry for rule {r}, but no rule state"
    let rs := rs.eraseHyp h i
    ruleStates := ruleStates.insert r rs
  return { fs with hyps := fs.hyps.erase h, ruleStates }

/-- Apply a goal diff to the state, adding and removing hypotheses as indicated
by the diff. `goal` must be the post-goal of `diff`. -/
def applyGoalDiff (idx : ForwardIndex) (goal : MVarId) (diff : GoalDiff)
    (fs : ForwardState) : MetaM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    if ! diff.fvarSubst.isEmpty then
      throwError "aesop: internal error: non-empty FVarSubst in GoalDiff is currently not supported"
    let mut fs := fs
    let mut ruleMatches := #[]
    for h in diff.removedFVars do
      fs := fs.eraseHyp h
    for h in diff.addedFVars do
      let rs ← idx.get (← h.getType)
      let (fs', ruleMatches') ← fs.addHypCore ruleMatches goal h rs
      fs := fs'
      ruleMatches := ruleMatches'
    return (fs, ruleMatches)

end Aesop.ForwardState
