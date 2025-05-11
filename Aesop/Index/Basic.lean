/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic
import Aesop.Rule.Name
import Aesop.RulePattern
import Aesop.Forward.Match.Types

open Lean Lean.Meta

namespace Aesop

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
  let path ← getConclusionDiscrTreeKeys type
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


/-- A rule that, according to the index, should be applied to the current goal.
In addition to the rule, this data structure contains information about how the
rule should be applied. For example, if the rule has rule patterns, we report
the substitutions obtained by matching the rule patterns against the current
goal. -/
structure IndexMatchResult (α : Type) where
  /-- The rule that should be applied. -/
  rule : α
  /-- Goal locations where the rule matched. The rule's `indexingMode`
  determines which locations can be contained in this set. -/
  locations : Std.HashSet IndexMatchLocation
  /-- Pattern substitutions for this rule that were found in the goal. `none`
  iff the rule doesn't have a pattern. -/
  patternSubsts? : Option (Std.HashSet Substitution)
  deriving Inhabited

namespace IndexMatchResult

instance [Ord α] : Ord (IndexMatchResult α) where
  compare r s := compare r.rule s.rule

instance [Ord α] : LT (IndexMatchResult α) :=
  ltOfOrd

instance [ToMessageData α] : ToMessageData (IndexMatchResult α) where
  toMessageData r := toMessageData r.rule

end Aesop.IndexMatchResult
