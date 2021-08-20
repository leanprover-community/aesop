/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Rule.Basic
import Aesop.RuleIndex
import Aesop.Percent
import Aesop.Rule.Tac
import Aesop.Util

namespace Aesop

open Lean
open Lean.Meta
open Std (RBMap mkRBMap)

/-! ### Normalisation Rules -/

structure NormRuleInfo where
  penalty : Int
  deriving Inhabited, DecidableEq

instance : Ord NormRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT NormRuleInfo :=
  ltOfOrd

instance : LE NormRuleInfo :=
  leOfOrd

abbrev NormRule' := Rule' NormRuleInfo
abbrev NormRule := NormRule' SerializableRuleTac

instance : ToFormat (NormRule' τ) where
  format r := f!"[{r.extra.penalty}] {r.name}"

def defaultNormPenalty : Int := 1


/-! ### Safe and Almost Safe Rules -/

inductive Safety
  | safe
  | almostSafe
  deriving Inhabited, DecidableEq

namespace Safety

instance : ToFormat Safety where
  format
    | safe => "safe"
    | almostSafe => "almostSafe"

end Safety

structure SafeRuleInfo where
  penalty : Int
  safety : Safety
  deriving Inhabited, DecidableEq

instance : Ord SafeRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT SafeRuleInfo :=
  ltOfOrd

instance : LE SafeRuleInfo :=
  leOfOrd

abbrev SafeRule' := Rule' SafeRuleInfo
abbrev SafeRule := SafeRule' SerializableRuleTac

instance : ToFormat (SafeRule' τ) where
  format r := f!"[{r.extra.penalty}/{r.extra.safety}] {r.name}"

def defaultSafePenalty : Int := 1


/-! ### Unsafe Rules -/

structure UnsafeRuleInfo where
  successProbability : Percent
  deriving Inhabited

instance : Ord UnsafeRuleInfo where
  compare i j := compare j.successProbability i.successProbability
  -- NOTE: Rule with greater success probabilities are considered smaller.
  -- This is because we take 'small' to mean 'high priority'.

instance : LT UnsafeRuleInfo :=
  ltOfOrd

instance : LE UnsafeRuleInfo :=
  leOfOrd

abbrev UnsafeRule' := Rule' UnsafeRuleInfo
abbrev UnsafeRule := UnsafeRule' SerializableRuleTac

instance : ToFormat (UnsafeRule' τ) where
  format r := f!"[{r.extra.successProbability.toHumanString}] {r.name}"


/-! ### Regular Rules -/

inductive RegularRule' τ
  | safe (r : SafeRule' τ)
  | «unsafe» (r : UnsafeRule' τ)
  deriving BEq

abbrev RegularRule := RegularRule' SerializableRuleTac

instance [Inhabited τ] : Inhabited (RegularRule' τ) where
  default := RegularRule'.«safe» arbitrary

namespace RegularRule'

instance : ToFormat (RegularRule' τ) where
  format
    | (safe r) => format r
    | («unsafe» r) => format r

def successProbability : RegularRule' τ → Percent
  | (safe r) => Percent.hundred
  | («unsafe» r) => r.extra.successProbability

def isSafe : RegularRule' τ → Bool
  | (safe _) => true
  | («unsafe» _) => false

def isUnsafe : RegularRule' τ → Bool
  | (safe _) => false
  | («unsafe» _) => true

def tac : RegularRule' τ → τ
  | (safe r) => r.tac
  | («unsafe» r) => r.tac

def name : RegularRule' τ → Name
  | (safe r) => r.name
  | («unsafe» r) => r.name

end RegularRule'
