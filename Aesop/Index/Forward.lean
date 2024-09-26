/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Rule.Forward
import Aesop.Index.Basic

open Lean Lean.Meta

namespace Aesop

/--
Maps expressions `T` to all tuples `(r, i)` where `r : ForwardRule`,
`i : PremiseIndex` and the `i`-th argument of the type of `r.expr` (counting
from zero) likely unifies with `T`.
-/
structure ForwardIndex where
  tree : DiscrTree (ForwardRule × PremiseIndex)
  deriving Inhabited

namespace ForwardIndex

/-- Insert a forward rule into the `ForwardIndex`. -/
def insert (r : ForwardRule) (idx : ForwardIndex) : MetaM ForwardIndex :=
  withReducible do
    let type ← inferType r.expr
    forallTelescopeReducing type λ args _ => do
      let args ← args.mapM fun e => do
        let type ← inferType e
        let deps ← getMVarsNoDelayed type
        return (e, HashSet.ofArray deps)
      let mut tree := idx.tree
      let mut previousDeps : HashSet MVarId := ∅
      for h : i in [:args.size] do
        let (arg, deps) := args[i]
        previousDeps := previousDeps.insertMany deps
        if ! previousDeps.contains arg.mvarId! then do
          tree ← tree.insert arg (r, ⟨i⟩) discrTreeConfig
      return ⟨tree⟩

/-- Get the forward rules whose maximal premises likely unify with `e`.
Each returned pair `(r, i)` contains a rule `r` and the index `i` of the premise
of `r` that likely unifies with `e`. -/
def get (idx : ForwardIndex) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  idx.tree.getUnify e discrTreeConfig

end Aesop.ForwardIndex
