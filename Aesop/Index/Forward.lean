/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Rule.Forward
import Batteries.Lean.Meta.DiscrTree

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

set_option linter.missingDocs false in
/--
Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`,
`i : PremiseIndex` and the `i`-th argument of the type of `r.expr` (counting
from zero) likely unifies with `T`. The `nameToRule` map indexes the forward
rules contained in `tree` by name.
-/
structure ForwardIndex where
  tree : DiscrTree (ForwardRule × PremiseIndex)
  nameToRule : PHashMap RuleName ForwardRule
  deriving Inhabited

namespace ForwardIndex

instance : EmptyCollection ForwardIndex :=
  ⟨⟨{}, {}⟩⟩

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

/-- Insert a forward rule into the `ForwardIndex`. -/
def insert (r : ForwardRule) (idx : ForwardIndex) : ForwardIndex := Id.run do
  let mut tree := idx.tree
  for cluster in r.slotClusters do
    for slot in cluster do
      let some discrTreeKeys := slot.typeDiscrTreeKeys?
        | continue
      tree := tree.insertCore discrTreeKeys (r, slot.premiseIndex)
  let nameToRule := idx.nameToRule.insert r.name r
  return { tree, nameToRule }

/-- Get the forward rules whose maximal premises likely unify with `e`.
Each returned pair `(r, i)` contains a rule `r` and the index `i` of the premise
of `r` that likely unifies with `e`. -/
def get (idx : ForwardIndex) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  getUnify idx.tree e

/-- Get the forward rule with the given rule name. -/
def getRuleWithName? (n : RuleName) (idx : ForwardIndex) : Option ForwardRule :=
  idx.nameToRule[n]

end Aesop.ForwardIndex
