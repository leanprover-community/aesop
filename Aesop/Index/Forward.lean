/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.Match.Types
import Aesop.Rule.Forward
import Aesop.Index.Basic
import Batteries.Lean.Meta.DiscrTree

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- Index for forward rules. -/
structure ForwardIndex where
  /-- Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`,
  `i : PremiseIndex` and the `i`-th argument of the type of `r.expr` (counting
  from zero) likely unifies with `T`. -/
  tree : DiscrTree (ForwardRule × PremiseIndex)
  /-- Indexes the forward rules contained in `tree` by name. -/
  nameToRule : PHashMap RuleName ForwardRule
  /-- Constant forward rules, i.e. forward rules that have no premises and no
  rule pattern. -/
  constRules : PHashSet ForwardRule
  deriving Inhabited

namespace ForwardIndex

instance : EmptyCollection ForwardIndex := by
  refine' ⟨{..}⟩ <;> exact {}

/-- Trace the rules contained in `idx` if `traceOpt` is enabled. -/
protected def trace (traceOpt : TraceOption) (idx : ForwardIndex) : CoreM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  else
    have : Ord (ForwardRule × PremiseIndex) := ⟨λ (r₁, _) (r₂, _) => compare r₁ r₂⟩
    have : BEq (ForwardRule × PremiseIndex) := ⟨λ (r₁, _) (r₂, _) => r₁ == r₂⟩
    let rs := idx.tree.values.qsortOrd.dedupSorted
    rs.forM λ (r, _) => do aesop_trace![traceOpt] r

/-- Merge two indices. -/
def merge (idx₁ idx₂ : ForwardIndex) : ForwardIndex where
  tree := idx₁.tree.mergePreservingDuplicates idx₂.tree
  nameToRule := idx₁.nameToRule.mergeWith idx₂.nameToRule λ _ r₁ _ => r₁
  constRules := idx₂.constRules.fold (init := idx₁.constRules) λ s r => s.insert r

/-- Insert a forward rule into the `ForwardIndex`. -/
def insert (r : ForwardRule) (idx : ForwardIndex) : ForwardIndex := Id.run do
  if r.isConstant then
    return {
      idx with
      constRules := idx.constRules.insert r
      nameToRule := idx.nameToRule.insert r.name r
    }
  else
    let mut tree := idx.tree
    for cluster in r.slotClusters do
      for slot in cluster do
        let some discrTreeKeys := slot.typeDiscrTreeKeys?
          | continue
        tree := tree.insertCore discrTreeKeys (r, slot.premiseIndex)
    let nameToRule := idx.nameToRule.insert r.name r
    return { idx with tree, nameToRule }

/-- Get the forward rules whose maximal premises likely unify with `e`.
Each returned pair `(r, i)` contains a rule `r` and the index `i` of the premise
of `r` that likely unifies with `e`. -/
def get (idx : ForwardIndex) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  getUnify idx.tree e

/-- Get the forward rule with the given rule name. -/
def getRuleWithName? (n : RuleName) (idx : ForwardIndex) : Option ForwardRule :=
  idx.nameToRule[n]

/-- Get forward rule matches for the constant forward rules (i.e., those with no
premises and no rule pattern). Accordingly, the returned matches contain no
hypotheses. -/
def getConstRuleMatches (idx : ForwardIndex) : Array ForwardRuleMatch :=
  idx.constRules.fold (init := #[]) λ ms r =>
    ms.push { rule := r, «match» := ∅ }

end Aesop.ForwardIndex
