/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean

import Aesop.Percent
import Aesop.Util

namespace Aesop

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM)

/-! ## Rules -/

structure Rule (α : Type) where
  name : Name
  tac : MVarId → MetaM (List MVarId)
  priorityInfo : α
  deriving Inhabited

instance [ToFormat α] : ToFormat (Rule α) where
  format r := f! "[{r.priorityInfo}] {r.name}" -- TODO don't output raw name?

instance : BEq (Rule α) where
  beq r s := r.name == s.name

instance [LT α] : LT (Rule α) where
  lt r s := r.priorityInfo < s.priorityInfo

instance [LT α] [DecidableRel (α := α) (· < ·)] :
    DecidableRel (α := Rule α) (· < ·) :=
  fun r s => inferInstanceAs $ Decidable (r.priorityInfo < s.priorityInfo)


/-! ### Normalisation Rules -/

def NormalizationRule := Rule Int

namespace NormalizationRule

instance : Inhabited NormalizationRule where
  default := Inhabited.default (α := Rule Int)

instance : BEq NormalizationRule where
  beq := BEq.beq (α := Rule Int)

instance : ToFormat NormalizationRule where
  format := format (α := Rule Int)

instance : LT NormalizationRule where
  lt r s := LT.lt (α := Rule Int) r s

instance : DecidableRel (α := NormalizationRule) (· < ·) :=
  inferInstanceAs $ DecidableRel (α := Rule Int) (· < ·)

protected def blt (r s : NormalizationRule) : Bool :=
  r < s

end NormalizationRule


/-! ### Safe Rules -/

inductive Safety
  | safe
  | almostSafe
  deriving DecidableEq, Inhabited

namespace Safety

instance : ToFormat Safety where
  format
    | safe => "safe"
    | almostSafe => "almostSafe"

end Safety

structure SafeRule extends Rule Int where
  safety : Safety
  deriving Inhabited

namespace SafeRule

instance : BEq SafeRule where
  beq r s := r.toRule == s.toRule

instance : ToFormat SafeRule where
  format r := format r.toRule

instance : LT SafeRule where
  lt r s := r.toRule < s.toRule

instance : DecidableRel (α := SafeRule) (· < ·) :=
  fun r s => inferInstanceAs $ Decidable (r.toRule < s.toRule)

protected def blt (r s : SafeRule) : Bool :=
  r < s

end SafeRule


/-! ### Unsafe Rules -/

def UnsafeRule := Rule Percent

namespace UnsafeRule

open Percent

instance : Inhabited UnsafeRule where
  default := Inhabited.default (α := Rule Percent)

instance : ToFormat UnsafeRule where
  format := format (α := Rule Percent)

instance : BEq UnsafeRule where
  beq := BEq.beq (α := Rule Percent)

instance : LT UnsafeRule where
  -- The priority info here is the success probability: favour larger
  -- probabilities.
  lt r s := r.priorityInfo > s.priorityInfo

instance : DecidableRel (α := UnsafeRule) (· < ·) :=
  fun r s => (inferInstance : Decidable (r.priorityInfo > s.priorityInfo))

protected def blt (r s : UnsafeRule) : Bool :=
  r < s

end UnsafeRule


/-! ### Regular Rules -/

inductive RegularRule
  | safeRule (r : SafeRule)
  | unsafeRule (r : UnsafeRule)
  deriving Inhabited, BEq

namespace RegularRule

instance : ToFormat RegularRule where
  format
    | (safeRule r) => "[safe] " ++ format (α := SafeRule) r
    | (unsafeRule r) => "[unsafe] " ++ format (α := UnsafeRule) r

def successProbability : RegularRule → Percent
  | (safeRule r) => ⟨100⟩
  | (unsafeRule r) => r.priorityInfo

def isSafe : RegularRule → Bool
  | (safeRule _) => true
  | (unsafeRule _) => false

def isUnsafe : RegularRule → Bool
  | (safeRule _) => false
  | (unsafeRule _) => true

def tac : RegularRule → MVarId → MetaM (List MVarId)
  | (safeRule r) => r.tac
  | (unsafeRule r) => r.tac

def name : RegularRule → Name
  | (safeRule r) => r.name
  | (unsafeRule r) => r.name

end RegularRule


/-! ## Rule Indexing Modes -/

inductive IndexingMode : Type
  | unindexed
  | indexTarget (target : Expr)
  deriving Inhabited, BEq

export IndexingMode (unindexed indexTarget)


/-! ## Rule Indices -/

structure RuleIndex (α : Type) where
  byTarget : DiscrTree α
  unindexed : Array α
  deriving Inhabited

namespace RuleIndex

open Std.Format in
instance [ToFormat α] : ToFormat (RuleIndex α) where
  format ri := Format.join
    [ "rules indexed by target:",
      indentD $ format ri.byTarget, -- TODO revisit
      line,
      "unindexed rules:",
      ri.unindexed.map format |>.toList |> unlines |> indentD ]

def empty : RuleIndex α where
  byTarget := DiscrTree.empty
  unindexed := #[] -- TODO keep these sorted?

def add [BEq α] (r : α) (imode : IndexingMode) (ri : RuleIndex α) :
    MetaM (RuleIndex α) :=
  match imode with
  | IndexingMode.unindexed => { ri with unindexed := ri.unindexed.push r }
  | IndexingMode.indexTarget tgt =>
    return { ri with byTarget := (← ri.byTarget.insert tgt r) }

def fromList [BEq α] (rs : List (α × IndexingMode)) : MetaM (RuleIndex α) :=
  rs.foldlM (λ rs ⟨r, imode⟩ => rs.add r imode) empty

def applicableByTargetRules (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array α) := do
  ri.byTarget.getMatch (← getMVarDecl goal).type

-- TODO remove Inhabited as soon as qsort doesn't require it any more.
def applicableRules [Inhabited α] [LT α] [DecidableRel (α := α) (· < ·)]
    (ri : RuleIndex α) (goal : MVarId) : MetaM (Array α) := do
  let rs₁ ← applicableByTargetRules ri goal
  let rs₂ := ri.unindexed -- TODO does it help if these are already sorted?
  return (rs₁ ++ rs₂).qsort (· < ·)

end RuleIndex


/-! ## Rule Set Members -/

inductive RuleSetMember
| normalizationRule (r : NormalizationRule) (imode : IndexingMode)
| normalizationSimpLemmas (s : SimpLemmas)
| unsafeRule (r : UnsafeRule) (imode : IndexingMode)
| safeRule (r : SafeRule) (imode : IndexingMode)


/-! ## Rule Set -/

structure RuleSet where
  normalizationRules : RuleIndex NormalizationRule
  normalizationSimpLemmas : SimpLemmas
  unsafeRules : RuleIndex UnsafeRule
  safeRules : RuleIndex SafeRule

namespace RuleSet

def empty : RuleSet :=
{ normalizationRules := RuleIndex.empty,
  normalizationSimpLemmas :=
    SimpLemmas.mk
      (DiscrTree.mk (Std.PersistentHashMap.empty))
      (DiscrTree.mk (Std.PersistentHashMap.empty))
      Std.PersistentHashSet.empty
      Std.PersistentHashSet.empty
      Std.PersistentHashSet.empty,
  unsafeRules := RuleIndex.empty,
  safeRules := RuleIndex.empty }

def add (rs : RuleSet) : RuleSetMember → MetaM RuleSet
  | RuleSetMember.normalizationRule r imode =>
    return { rs with normalizationRules := (← rs.normalizationRules.add r imode) }
  | RuleSetMember.normalizationSimpLemmas s =>
    return { rs with normalizationSimpLemmas := rs.normalizationSimpLemmas.merge s }
  | RuleSetMember.unsafeRule r imode =>
    return { rs with unsafeRules := (← rs.unsafeRules.add r imode )}
  | RuleSetMember.safeRule r imode =>
    return { rs with safeRules := (← rs.safeRules.add r imode )}

def fromList (rs : List RuleSetMember) : MetaM RuleSet :=
  rs.foldlM (λ rs r => rs.add r) empty

def applicableNormalizationRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array NormalizationRule) :=
  rs.normalizationRules.applicableRules goal

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array UnsafeRule) :=
  rs.unsafeRules.applicableRules goal

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array SafeRule) :=
  rs.safeRules.applicableRules goal

end RuleSet

end Aesop
