/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Rule.Forward
import Aesop.RuleTac.ElabRuleTerm
import Aesop.RuleTac.Forward.Basic
import Aesop.Script.SpecificTactics
import Batteries.Lean.Meta.SavedState
import Batteries.Lean.Meta.UnusedNames
import Batteries.Data.BinomialHeap.Basic

open Lean Lean.Meta
open Batteries (BinomialHeap)
open ExceptToEmoji (toEmoji)

set_option linter.missingDocs true

namespace Aesop

/-- Elaborate the term of a forward rule in the current goal. -/
def elabForwardRuleTerm (goal : MVarId) : RuleTerm → MetaM Expr
  | .const n => mkConstWithFreshMVarLevels n
  | .term stx =>
    (withFullElaboration $ elabRuleTermForApplyLikeMetaM goal stx).run'

/-- A substitution maps premise indices to assignments. -/
abbrev Substitution := AssocList PremiseIndex Expr

namespace Substitution

/-- Merge two substitutions. Precondition: the substitutions are compatible, so
if `s₁[x]` and `s₂[x]` are both defined, they must be the same value. -/
def mergeCompatible (s₁ s₂ : Substitution) : Substitution :=
  s₂.foldl (init := s₁) λ s k v =>
    assert! let r? := s.find? k; r?.isNone || r? == some v
    s.insert k v

end Substitution

/-- A match associates hypotheses to (a prefix of) the slots of a slot
cluster. -/
structure Match where
  /-- Hyps for each slot, in reverse order. If there are `n` slots, the `i`th
  hyp in `revHyps` is the hyp associated with the slot with index `n - i`. -/
  revHyps : List FVarId
  /-- `revHyps` is nonempty --/
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

end Match

set_option linter.missingDocs false in
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
      m.insert e (ms, hs.erase hyp)
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
`slot` with substitution `sub` (and hence `sub` contains a mapping for each
variable in `slot.common`). -/
def addHyp (vmap : VariableMap) (slot : Slot) (sub : Substitution)
    (hyp : FVarId) : VariableMap :=
  slot.common.fold (init := vmap) λ vmap var =>
    if let some inst := sub.find? var then
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
    Std.HashSet FVarId := Id.run do
  let common := slot.common.toArray
  if h : 0 < common.size then
    let mut hyps := slotHyps common[0] |> PersistentHashSet.toHashSet
    for var in common[1:] do
      let hyps' := slotHyps var
      hyps := hyps.filter (hyps'.contains ·)
    return hyps
  else
    panic! "no common variables"
where
  slotHyps (var : PremiseIndex) : PHashSet FVarId :=
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
  withAesopTraceNode .debug (λ r => return m!"{toEmoji r} match against premise {slot.premiseIndex}: {hypType} ≟ {inputHypType}") do
    if ← isDefEq inputHypType hypType then
      /- Note: This was over `slot.common` and not `slot.deps`. We need `slot.deps`
      because, among other issues, `slot.common` is empty in the first slot. Even though
      we don't have dependencies, we still need to keep track of the subs of hyp.
      Otherwise, we would trigger the first panic in `AddHypothesis`.-/
      let mut subst : Substitution := ∅
      for var in slot.deps do
        let some varMVarId := premises[var.toNat]?
          | throwError "aesop: internal error: matchPremise?: dependency with index {var}, but only {premises.size} premises"
        let mvar := .mvar varMVarId
        let assignment ← instantiateMVars mvar
        if assignment == mvar then
          throwError "aesop: internal error: matchPremise?: while matching hyp {hyp.name}: no assignment for variable {var}"
        subst := subst.insert var assignment
      return subst
    else
      return none

/-- Add a match to the cluster state. Returns the new cluster state and any new
complete matches for this cluster. -/
partial def addMatchCore (newCompleteMatches : Array Match)
      (cs : ClusterState) (m : Match) :
      ClusterState × Array Match := Id.run do
    let mut cs := cs
    let slotIdx := m.level
    if slotIdx.toNat == cs.slots.size - 1 then
      cs := { cs with completeMatches := cs.completeMatches.push m }
      return (cs, newCompleteMatches.push m)
    else
      let nextSlot := cs.slot! $ slotIdx + 1
      cs := { cs with
        variableMap := cs.variableMap.addMatch nextSlot m
      }
      let mut newCompleteMatches := newCompleteMatches
      for hyp in cs.variableMap.findHyps nextSlot m.subst do
        let m := { revHyps := hyp :: m.revHyps, subst := m.subst }
        let (cs', newCompleteMatches') ← cs.addMatchCore newCompleteMatches m
        cs := cs'
        newCompleteMatches := newCompleteMatches'
      return (cs, newCompleteMatches)

@[inherit_doc addMatchCore]
def addMatch (cs : ClusterState) (m : Match) : ClusterState × Array Match :=
  addMatchCore #[] cs m

/-- Add a hypothesis to the cluster state. `subst` must be the substitution that
results from applying `h` to `slot`. -/
def addHypCore (newCompleteMatches : Array Match) (cs : ClusterState)
    (slot : Slot) (h : FVarId) (subst : Substitution) :
    ClusterState × Array Match := Id.run do
  let mut cs :=
    { cs with variableMap := cs.variableMap.addHyp slot subst h }
  if slot.index.toNat == 0 then
    return ← cs.addMatch { revHyps := [h], subst }
  else
    let mut newCompleteMatches := newCompleteMatches
    for pm in cs.variableMap.findMatches slot subst do
      let subst := subst.mergeCompatible pm.subst
      let m := { revHyps := h :: pm.revHyps, subst }
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
  return addHypCore #[] cs slot h subst

/-- Erase a hypothesis from the cluster state. -/
def eraseHyp (h : FVarId) (pi : PremiseIndex) (cs : ClusterState) :
    ClusterState := Id.run do
  let some slot := cs.findSlot? pi
    | return cs
  { cs with variableMap := cs.variableMap.eraseHyp h slot.index }

end ClusterState

set_option linter.missingDocs false in
/-- A complete match contains complete matches for each slot cluster. This means
there is one match for each slot cluster and each such match contains a
hypothesis for each of the slots. -/
structure CompleteMatch where
  clusterMatches : Array Match
  deriving Inhabited

namespace CompleteMatch

/-- Given a complete match `m` for `r`, get arguments to `r` contained in the
match's slots and substitution. -/
def reconstructArgs (r : ForwardRule) (m : CompleteMatch) :
    Array Expr := Id.run do
  let mut slotHyps : Std.HashMap PremiseIndex FVarId := ∅
  for h : i in [:r.slotClusters.size] do
    let cluster := r.slotClusters[i]
    let some m := m.clusterMatches[i]?
      | panic! s!"match for rule {r.name} is not complete: no cluster match for cluster {i}"
    let hyps := m.revHyps.toArray.reverse
    for h' : j in [:cluster.size] do
      let slot := cluster[j]
      let some hyp := hyps[j]?
        | panic! s!"match for rule {r.name} is not complete: no hyp for slot with premise index {slot.premiseIndex} in cluster {i}"
      slotHyps := slotHyps.insert slot.premiseIndex hyp

  let mut subst : Substitution := ∅
  for m in m.clusterMatches do
    subst := subst.mergeCompatible m.subst

  let mut args := Array.mkEmpty r.numPremises
  for i in [:r.numPremises] do
    if let some hyp := slotHyps.get? ⟨i⟩ then
      args := args.push (.fvar hyp)
    else if let some inst := subst.find? ⟨i⟩ then
      args := args.push inst
    else
      panic! s!"match for rule {r.name} is not complete: no hyp or instantiation for premise {i}"

  return args

end CompleteMatch

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardRuleMatch where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : CompleteMatch
  deriving Nonempty

namespace ForwardRuleMatch

/-- Compare two queue entries by rule priority. Higher-priority rules are
considered less (since the queues are min-queues). -/
protected def le (m₁ m₂ : ForwardRuleMatch) : Bool :=
  match m₁.rule.prio, m₂.rule.prio with
  | .normSafe x, .normSafe y => x ≤ y
  | .unsafe x, .unsafe y => x ≥ y
  | _, _ => panic! "comparing ForwardRuleMatches with different priority types"

/-- Returns `true` if any hypothesis contained in `m` satisfies `f`. -/
def anyHyp (m : ForwardRuleMatch) (f : FVarId → Bool) : Bool :=
  m.match.clusterMatches.any (·.revHyps.any f)

/-- Construct the proof of the new hypothesis represented by `m`. -/
def getProof (goal : MVarId) (m : ForwardRuleMatch) : MetaM Expr :=
  goal.withContext do
    let e ← elabForwardRuleTerm goal m.rule.term
    return mkAppN e (m.match.reconstructArgs m.rule)

/-- Apply a forward rule match to a goal. This adds the hypothesis corresponding
to the match to the local context. -/
def apply (goal : MVarId) (m : ForwardRuleMatch) : ScriptM (MVarId × FVarId) :=
  goal.withContext do
    let name ← getUnusedUserName forwardHypPrefix
    let prf ← m.getProof goal
    let type ← inferType prf
    let hyp := { userName := name, value := prf, type }
    let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
      | unreachable!
    return (goal, hyp)

end ForwardRuleMatch

/-- A complete match queue. -/
abbrev CompleteMatchQueue := BinomialHeap ForwardRuleMatch ForwardRuleMatch.le

namespace CompleteMatchQueue

/-- Drop elements satisfying `f` from the front of `queue` until we reach
an element that does not satisfy `f` (or until the queue is empty). -/
partial def dropInitial (queue : CompleteMatchQueue)
    (f : ForwardRuleMatch → Bool) : CompleteMatchQueue :=
  match queue.deleteMin with
  | none => queue
  | some (m, queue') =>
    if f m then
      dropInitial queue' f
    else
      queue

end CompleteMatchQueue

/-- Forward state for one rule. -/
structure RuleState where
  /-- The rule to which this state belongs. -/
  rule : ForwardRule
  /-- States for each of the rule's slot clusters. -/
  clusterStates : Array ClusterState
  deriving Inhabited

/-- The initial (empty) rule state for a given forward rule. -/
def ForwardRule.initialRuleState (r : ForwardRule) : RuleState :=
  let clusterStates := r.slotClusters.map λ slots =>
    { slots, variableMap := ∅, completeMatches := {} }
  { rule := r, clusterStates }

namespace RuleState

/-- Add a hypothesis to the rule state. Returns the new rule state and any newly
completed matches. If `h` does not match premise `pi`, nothing happens. -/
def addHyp (goal : MVarId) (h : FVarId) (pi : PremiseIndex) (rs : RuleState) :
    MetaM (RuleState × Array CompleteMatch) := do
  let some ruleExpr ← observing? $ elabForwardRuleTerm goal rs.rule.term
    | return (rs, #[])
  withNewMCtxDepth do
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

/-- State representing the (partial or complete) matches of a given set of
forward rules in a given local context. -/
structure ForwardState where
  /-- Map from each rule's name to its `RuleState`-/
  ruleStates : PHashMap RuleName RuleState
  /-- Queue of complete matches for norm rules. -/
  normQueue : CompleteMatchQueue
  /-- Queue of complete matches for safe rules. -/
  safeQueue : CompleteMatchQueue
  /-- Queue of complete matches for unsafe rules. -/
  unsafeQueue : CompleteMatchQueue
  /-- Hypotheses that were removed from the local context. Matches containing
  such hyps are not removed from the complete match queues. Instead, the hyps
  are added to this set and when a match is popped from the queues, we check
  whether it contains any removed hyps. -/
  erasedHyps : PHashSet FVarId
 deriving Inhabited

namespace ForwardState

instance : EmptyCollection ForwardState where
  emptyCollection := by refine' {..} <;> first | exact ∅ | exact .empty

/-- Add a complete match entry to the forward state's complete match queue for
`phase`. -/
def addForwardRuleMatch (m : ForwardRuleMatch) (phase : PhaseName)
    (fs : ForwardState) : ForwardState :=
  match phase with
  | .norm => { fs with normQueue := fs.normQueue.insert m }
  | .safe => { fs with safeQueue := fs.safeQueue.insert m }
  | .unsafe => { fs with unsafeQueue := fs.unsafeQueue.insert m }

/-- Add a hypothesis to the forward state. If `fs` represents a local context
`lctx`, then `fs.addHyp h ms` represents `lctx` with `h` added. `ms` must
overapproximate the rules for which `h` may unify with a maximal premise. -/
def addHyp (goal : MVarId) (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : MetaM ForwardState := do
  goal.withContext do
  withConstAesopTraceNode .debug (return m!"add hyp {Expr.fvar h}") do
    ms.foldlM (init := fs) λ fs (r, i) => do
      withConstAesopTraceNode .debug (return m!"rule {r.name}, premise {i}") do
        let rs := fs.ruleStates.find? r.name |>.getD r.initialRuleState
        let (rs, completeMatches) ← rs.addHyp goal h i
        let fs := { fs with ruleStates := fs.ruleStates.insert r.name rs }
        completeMatches.foldlM (init := fs) λ fs m => do
          aesop_trace[forward] "new complete match with args {m.reconstructArgs r}"
          let m := { rule := r, «match» := m }
          return fs.addForwardRuleMatch m r.name.phase

/-- Remove a hypothesis from the forward state. If `fs` represents a local
context `lctx`, then `fs.eraseHyp h ms` represents `lctx` with `h` removed. `ms`
must contain all rules for which `h` may unify with a maximal premise. -/
def eraseHyp (h : FVarId) (ms : Array (ForwardRule × PremiseIndex))
    (fs : ForwardState) : ForwardState := Id.run do
  let mut ruleStates := fs.ruleStates
  for (r, i) in ms do
    let some rs := ruleStates.find? r.name
      | continue
    let rs := rs.eraseHyp h i
    ruleStates := ruleStates.insert r.name rs
  return { fs with ruleStates, erasedHyps := fs.erasedHyps.insert h }

/-- Drop complete matches containing an erased hyp from the complete match
queues. Note that we only drop matches at the front of the queue, until we reach
the first match containing no erased hyps. -/
def dropForwardMatchesWithErasedHyps (fs : ForwardState) : ForwardState := {
  fs with
  normQueue := fs.normQueue.dropInitial (·.anyHyp fs.erasedHyps.contains)
  safeQueue := fs.safeQueue.dropInitial (·.anyHyp fs.erasedHyps.contains)
  unsafeQueue := fs.unsafeQueue.dropInitial (·.anyHyp fs.erasedHyps.contains)
}

/-- Get the first norm match (if any) without dropping it from the norm complete
match queue. Use `dropForwardMatchesWithErasedHyps` to ensure that the match does
not contain erased hyps. -/
def peekNormMatch? (fs : ForwardState) : Option ForwardRuleMatch :=
  fs.normQueue.head?

/-- Remove first norm match (if any) from the norm complete match queue. Use
`dropForwardMatchesWithErasedHyps` to ensure that the match does not contain
erased hyps. -/
def dropNormMatch (fs : ForwardState) : ForwardState :=
  { fs with normQueue := fs.normQueue.tail }

/-- Get the first safe match (if any) without dropping it from the safe complete
match queue. Use `dropForwardMatchesWithErasedHyps` to ensure that the match does
not contain erased hyps. -/
def peekSafeMatch? (fs : ForwardState) : Option ForwardRuleMatch :=
  fs.safeQueue.head?

/-- Remove first safe match (if any) from the safe complete match queue. Use
`dropForwardMatchesWithErasedHyps` to ensure that the match does not contain
erased hyps. -/
def dropSafeMatch (fs : ForwardState) : ForwardState :=
  { fs with safeQueue := fs.safeQueue.tail }

/-- Get all unsafe complete matches and remove them from the unsafe match
queue. -/
partial def getResetUnsafeMatches (fs : ForwardState) :
    Array ForwardRuleMatch × ForwardState :=
  let ms := go #[] fs.unsafeQueue
  (ms, { fs with unsafeQueue := ∅ })
where
  go (acc : Array ForwardRuleMatch) (q : CompleteMatchQueue) :
      Array ForwardRuleMatch :=
    match q.deleteMin with
    | none => acc
    | some (m, q) =>
      if m.anyHyp (fs.erasedHyps.contains ·) then
        go acc q
      else
        go (acc.push m) q

/-- Get the first complete match. Norm matches are prioritised over safe matches
and safe over unsafe matches. Use `dropForwardMatchesWithErasedHyps` to ensure
that the match does not contain erased hyps. -/
def popMatch? (fs : ForwardState) : Option (ForwardRuleMatch × ForwardState) :=
  if let some (m, queue) := fs.normQueue.deleteMin then
    (m, { fs with normQueue := queue })
  else if let some (m, queue) := fs.safeQueue.deleteMin then
    (m, { fs with safeQueue := queue })
  else if let some (m, queue) := fs.unsafeQueue.deleteMin then
    (m, { fs with unsafeQueue := queue })
  else
    none

end Aesop.ForwardState
