/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.RulePattern
import Aesop.Util.Basic
import Aesop.Util.UnionFind

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- A slot represents a maximal premise of a forward rule, i.e. a premise with
no forward dependencies. The goal of forward reasoning is to assign a
hypothesis to each slot in such a way that the assignments agree on all
variables shared between them.

Exceptionally, a slot can also represent the rule pattern substitution. Rules
with a rule pattern have exactly one such slot, which is assigned an arbitrary
premise index. -/
structure Slot where
  /-- Discrimination tree keys for the type of this slot. If the slot is for the
  rule pattern, it is not associated with a premise, so doesn't have
  discrimination tree keys. -/
  typeDiscrTreeKeys? : Option (Array DiscrTree.Key)
  /-- Index of the slot. Slots are always part of a list of slots, and `index`
  is the 0-based index of this slot in that list. -/
  index : SlotIndex
  /-- 0-based index of the premise represented by this slot in the rule type.
  Note that the slots array may use a different ordering than the original
  order of premises, so we *don't* always have `index ≤ premiseIndex`. Rule
  pattern slots are assigned an arbitrary premise index. -/
  premiseIndex : PremiseIndex
  /-- The previous premises that the premise of this slot depends on. -/
  deps : Std.HashSet PremiseIndex
  /-- Common variables shared between this slot and the previous slots. -/
  common : Std.HashSet PremiseIndex
  /-- The forward dependencies of this slot. These are all the premises that
  appear in slots *after* this one. -/
  forwardDeps : Array PremiseIndex
  deriving Inhabited

local instance : BEq Slot :=
  ⟨λ s₁ s₂ => s₁.premiseIndex == s₂.premiseIndex⟩

local instance : Hashable Slot :=
  ⟨(hash ·.premiseIndex)⟩

/-- Information about the decomposed type of a forward rule. -/
structure ForwardRuleInfo where
  /-- The rule's number of premises. -/
  numPremises : Nat
  /-- The number of distinct level parameters and level metavariables occurring
  in the rule's type. We expect that these turn into level metavariables when
  the rule is elaborated. -/
  numLevelParams : Nat
  /-- Slots representing the maximal premises of the forward rule, partitioned
  into metavariable clusters. -/
  slotClusters : Array (Array Slot)
  /-- The premises that appear in the rule's conclusion. -/
  conclusionDeps : Array PremiseIndex
  /-- The rule's rule pattern and the premise index that was assigned to it. -/
  rulePatternInfo? : Option (RulePattern × PremiseIndex)
  deriving Inhabited

namespace ForwardRuleInfo

/-- Is this rule a constant rule (i.e., does it have neither premises nor a rule
pattern)? -/
def isConstant (r : ForwardRuleInfo) : Bool :=
  r.numPremises == 0 && r.rulePatternInfo?.isNone

/-- Construct a `ForwardRuleInfo` for the theorem `thm`. -/
def ofExpr (thm : Expr) (rulePattern? : Option RulePattern)
    (immediate : UnorderedArraySet PremiseIndex) : MetaM ForwardRuleInfo :=
  withNewMCtxDepth do
  let e ← instantiateMVars (← inferType thm)
  let numLevelParams :=
    (collectLevelParams {} e).params.size +
    (collectLevelMVars {} e).result.size
  let (premises, _, conclusion) ← withReducible $ forallMetaTelescope e
  let premises := premises.map (·.mvarId!)
  let mut premiseToIdx : Std.HashMap MVarId PremiseIndex := ∅
  for h : i in [:premises.size] do
    premiseToIdx := premiseToIdx.insert premises[i] ⟨i⟩
  let mut slots : Array Slot := Array.mkEmpty premises.size
  let mut allDeps : Std.HashSet PremiseIndex := ∅
  for h : i in [:premises.size] do
    let mvarId := premises[i]
    let typeDiscrTreeKeys ← mkDiscrTreePath (← mvarId.getType)
    let mut deps : Std.HashSet PremiseIndex := ∅
    for dep in ← mvarId.getMVarDependencies do
      if let some idx := premiseToIdx[dep]? then
        deps := deps.insert idx
    -- We update the `default` fields with correct info later.
    slots := slots.push {
      typeDiscrTreeKeys? := typeDiscrTreeKeys
      index := default
      premiseIndex := ⟨i⟩
      common := default
      forwardDeps := default
      deps
    }
    allDeps := allDeps.insertMany deps
  -- Slots are created only for premises which are maximal, i.e. which do not
  -- appear in any other premises, and which are not bound by the rule pattern.
  let patBoundPremises : Std.HashSet PremiseIndex :=
    rulePattern?.map (.ofArray $ ·.boundPremises.map (⟨·⟩)) |>.getD ∅
  slots := slots.filter λ s =>
    let idx := s.premiseIndex
    ! allDeps.contains idx && ! patBoundPremises.contains idx &&
    immediate.contains idx
  -- If the rule has a pattern, an additional slot is created for the rule
  -- pattern substitution. Again, we update the `default` fields with correct
  -- info later.
  if rulePattern?.isSome then
    slots := slots.push {
      typeDiscrTreeKeys? := none
      index := default
      premiseIndex := ⟨premises.size⟩
      common := default
      deps := patBoundPremises
      forwardDeps := default
    }
  -- Slots are clustered into metavariable clusters and sorted as indicated
  -- below.
  let slotClusters := cluster (·.deps.toArray) slots |>.map sortSlots
  -- The sorting ensures that for each slot in a cluster (except the first), the
  -- slot has some variables in common with the previous slots.
  assert! ! slotClusters.any λ cluster => cluster.any λ slot =>
    slot.index.toNat > 0 && slot.common.isEmpty
  let conclusionDeps := (← getMVars conclusion).filterMap (premiseToIdx[·]?)
  let rulePatternInfo? := rulePattern?.map (·, ⟨premises.size⟩)
  return {
    numPremises := premises.size
    slotClusters, rulePatternInfo?, conclusionDeps, numLevelParams
  }
where
  /-- Sort slots such that each slot has at least one variable in common with
  the previous slots. -/
  sortSlots (slots : Array Slot) : Array Slot := Id.run do
    if slots.isEmpty then
      panic! "empty slot cluster"
    -- Slots with more dependencies are preferred. In case of a tie, later slots
    -- are preferred since they tend to be more specific.
    have : Ord Slot := ⟨λ x y =>
      compareOn (·.deps.size) x y
      |>.then (compareOn (·.premiseIndex) x y)
    ⟩
    let firstSlot := slots.maxI
    let mut unseen := slots |>.erase firstSlot
    let firstSlotForwardDeps : Std.HashSet PremiseIndex :=
      unseen.foldl (init := ∅) λ deps s => deps.insertMany s.deps
    let firstSlot := {
      firstSlot with
      index := ⟨0⟩
      common := ∅
      forwardDeps := firstSlotForwardDeps.toArray
    }
    let mut newSlots := Array.mkEmpty slots.size |>.push firstSlot
    let mut previousDeps := firstSlot.deps
    let mut i := 1
    while newSlots.size != slots.size do
      let candidates := unseen.filter (·.deps.any (previousDeps.contains ·))
      let some slot := candidates.max?
        | panic! "no suitable slot found"
      unseen := unseen.erase slot
      let common := previousDeps.filter (slot.deps.contains ·)
      let forwardDeps : Std.HashSet PremiseIndex :=
        unseen.foldl (init := ∅) λ deps s => deps.insertMany s.deps
      let forwardDeps := forwardDeps.toArray
      newSlots := newSlots.push { slot with index := ⟨i⟩, common, forwardDeps }
      previousDeps := previousDeps.insertMany slot.deps
      i := i + 1
    return newSlots

end ForwardRuleInfo
