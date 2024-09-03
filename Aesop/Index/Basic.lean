/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic
import Aesop.Rule.Name
import Aesop.RulePattern

open Lean Lean.Meta

namespace Aesop

-- This value controls whether we use 'powerful' reductions, e.g. iota, when
-- indexing Aesop rules. See the `DiscrTree` docs for details.
def discrTreeConfig : WhnfCoreConfig := { iota := false }

inductive IndexingMode : Type
  | unindexed
  | target (keys : Array DiscrTree.Key)
  | hyps (keys : Array DiscrTree.Key)
  | or (imodes : Array IndexingMode)
  deriving Inhabited

namespace IndexingMode

protected partial def format : IndexingMode → Format
  | unindexed => "unindexed"
  | target keys => f!"target {keys}"
  | hyps keys => f!"hyps {keys}"
  | or imodes => f!"or {imodes.map IndexingMode.format}"

instance : ToFormat IndexingMode :=
  ⟨IndexingMode.format⟩

def targetMatchingConclusion (type : Expr) : MetaM IndexingMode := do
  let path ← getConclusionDiscrTreeKeys type discrTreeConfig
  return target path

def hypsMatchingConst (decl : Name) : MetaM IndexingMode := do
  let path ← getConstDiscrTreeKeys decl
  return hyps path

end IndexingMode


inductive IndexMatchLocation
  | none
  | target
  | hyp (ldecl : LocalDecl)
  deriving Inhabited

namespace IndexMatchLocation

instance : ToMessageData IndexMatchLocation where
  toMessageData
    | none => "none"
    | target => "target"
    | hyp ldecl => m!"hyp {ldecl.userName}"

instance : BEq IndexMatchLocation where
  beq
    | none, none => true
    | target, target => true
    | hyp ldecl₁, hyp ldecl₂ => ldecl₁.fvarId == ldecl₂.fvarId
    | _, _ => false

instance : Ord IndexMatchLocation where
  compare
    | target, target => .eq
    | target, none => .lt
    | target, hyp .. => .lt
    | none, target => .gt
    | none, none => .eq
    | none, hyp .. => .lt
    | hyp .., target => .gt
    | hyp .., none => .gt
    | hyp ldecl₁, hyp ldecl₂ => ldecl₁.fvarId.name.cmp ldecl₂.fvarId.name

instance : Hashable IndexMatchLocation where
  hash
    | none => 7
    | target => 13
    | hyp ldecl => mixHash 17 $ hash ldecl.fvarId

end IndexMatchLocation


structure IndexMatchResult (α : Type) where
  rule : α
  locations : Std.HashSet IndexMatchLocation
  patternInstantiations : Std.HashSet RulePatternInstantiation
  deriving Inhabited

namespace IndexMatchResult

instance [Ord α] : Ord (IndexMatchResult α) where
  compare r s := compare r.rule s.rule

instance [Ord α] : LT (IndexMatchResult α) :=
  ltOfOrd

instance [ToMessageData α] : ToMessageData (IndexMatchResult α) where
  toMessageData r := toMessageData r.rule

end Aesop.IndexMatchResult
