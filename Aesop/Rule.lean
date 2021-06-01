/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean.Elab.Tactic.Basic

import Aesop.Percent
import Aesop.Util

namespace Aesop

open Lean
open Lean.Meta
open Lean.Elab.Tactic (TacticM)

/-! ## Rule Indexing Modes -/

inductive IndexingMode : Type
  | unindexed
  | indexTargetHead (hd : Name)

export IndexingMode (unindexed indexTargetHead)


/-! ## Rules -/

structure Rule (α : Type) where
  tac : TacticM Unit
  description : Format
  penalty : α
  deriving Inhabited

instance [ToFormat α] : ToFormat (Rule α) where
  format r := f! "[{r.penalty}] {r.description}"

instance [LT α] : LT (Rule α) where
  lt r s := r.penalty < s.penalty

instance [LT α] [DecidableRel (α := α) (· < ·)] :
    DecidableRel (α := Rule α) (· < ·) :=
  fun r s => (inferInstance : Decidable (r.penalty < s.penalty))


def NormalizationRule := Rule Int

namespace NormalizationRule

instance : ToFormat NormalizationRule where
  format := format (α := Rule Int)

instance : LT NormalizationRule where
  lt r s := LT.lt (α := Rule Int) r s

instance : DecidableRel (α := NormalizationRule) (· < ·) :=
  (inferInstance : DecidableRel (α := Rule Int) (· < ·))

protected def blt (r s : NormalizationRule) : Bool :=
  r < s

end NormalizationRule


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

namespace SafeRule

instance : ToFormat SafeRule where
  format r := format r.toRule

instance : LT SafeRule where
  lt r s := r.toRule < s.toRule

instance : DecidableRel (α := SafeRule) (· < ·) :=
  fun r s => (inferInstance : Decidable (r.toRule < s.toRule))

protected def blt (r s : SafeRule) : Bool :=
  r < s

end SafeRule


def UnsafeRule := Rule Percent

namespace UnsafeRule

open Percent

instance : ToFormat UnsafeRule where
  format := format (α := Rule Percent)

instance : LT UnsafeRule where
  -- The penalty is really the success probability: favour larger success
  lt r s := r.penalty > s.penalty

instance : DecidableRel (α := UnsafeRule) (· < ·) :=
  fun r s => (inferInstance : Decidable (r.penalty > s.penalty))

protected def blt (r s : UnsafeRule) : Bool :=
  r < s

end UnsafeRule


inductive RegularRule
  | safeRule (r : SafeRule)
  | unsafeRule (r : UnsafeRule)

namespace RegularRule

instance : ToFormat RegularRule where
  format
    | (safeRule r) => "[safe] " ++ format (α := SafeRule) r
    | (unsafeRule r) => "[unsafe] " ++ format (α := UnsafeRule) r

-- TODO: we cannot write toRule as the penalty type parameter is different

def successProbability : RegularRule → Percent
  | (safeRule r) => ⟨100⟩
  | (unsafeRule r) => r.penalty

def isSafe : RegularRule → Bool
  | (safeRule _) => true
  | (unsafeRule _) => false

def isUnsafe : RegularRule → Bool
  | (safeRule _) => false
  | (unsafeRule _) => true

end RegularRule


/-! ## Rule Indices -/

end Aesop
