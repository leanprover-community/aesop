/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Rule.Forward
import Aesop.Index.Basic
import Batteries.Lean.Meta.DiscrTree

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

set_option linter.missingDocs false in
/--
Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`,
`i : PremiseIndex` and the `i`-th argument of the type of `r.expr` (counting
from zero) likely unifies with `T`.
-/
structure ForwardIndex where
  tree : DiscrTree (ForwardRule × PremiseIndex)
  deriving Inhabited

namespace ForwardIndex

instance : EmptyCollection ForwardIndex :=
  ⟨⟨{}⟩⟩

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
def merge (idx₁ idx₂ : ForwardIndex) : ForwardIndex :=
  ⟨idx₁.tree.mergePreservingDuplicates idx₂.tree⟩

/-- Insert a forward rule into the `ForwardIndex`. -/
def insert (r : ForwardRule) (idx : ForwardIndex) : ForwardIndex := Id.run do
  let mut tree := idx.tree
  for cluster in r.slotClusters do
    for slot in cluster do
      tree := tree.insertCore slot.typeDiscrTreeKeys (r, slot.premiseIndex)
  return ⟨tree⟩

/-- Get the forward rules whose maximal premises likely unify with `e`.
Each returned pair `(r, i)` contains a rule `r` and the index `i` of the premise
of `r` that likely unifies with `e`. -/
def get (idx : ForwardIndex) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  idx.tree.getUnify e discrTreeConfig

end Aesop.ForwardIndex
