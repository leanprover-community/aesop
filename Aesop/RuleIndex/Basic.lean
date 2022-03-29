/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean
open Lean.Meta
open Std (RBMap)

namespace Aesop

inductive IndexingMode : Type
  | unindexed
  | target (keys : Array DiscrTree.Key)
  | hyps (keys : Array DiscrTree.Key)
  deriving Inhabited

namespace IndexingMode

def targetMatchingConclusion (type : Expr) : MetaM IndexingMode := do
  let path ← withoutModifyingState do
    let (_, _, conclusion) ← forallMetaTelescope type
    DiscrTree.mkPath conclusion
    -- We use a meta telescope because `DiscrTree.mkPath` ignores metas (they
    -- turn into `Key.star`) but not fvars.
  return IndexingMode.target path

end IndexingMode


inductive IndexMatchLocation
  | target
  | hyp (ldecl : LocalDecl)
  | none

namespace IndexMatchLocation

instance : ToMessageData IndexMatchLocation where
  toMessageData
    | target => "target"
    | hyp ldecl => m!"hyp {ldecl.userName}"
    | none => "none"

end IndexMatchLocation


structure IndexMatchResult (α : Type) where
  rule : α
  matchLocations : Array IndexMatchLocation
  deriving Inhabited

namespace RuleIndexMatchResult

instance [Ord α] : Ord (IndexMatchResult α) where
  compare r s := compare r.rule s.rule

instance [Ord α] : LT (IndexMatchResult α) :=
  ltOfOrd

instance [ToMessageData α] : ToMessageData (IndexMatchResult α) where
  toMessageData r := toMessageData r.rule

end Aesop.RuleIndexMatchResult
