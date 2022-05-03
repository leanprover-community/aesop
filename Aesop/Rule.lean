/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Rule.Basic
import Aesop.RuleIndex
import Aesop.Percent
import Aesop.Util

namespace Aesop

open Lean
open Lean.Meta
open Std (RBMap mkRBMap)

/-! ### Normalisation Rules -/

structure NormRuleInfo where
  penalty : Int
  deriving Inhabited

instance : Ord NormRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT NormRuleInfo :=
  ltOfOrd

instance : LE NormRuleInfo :=
  leOfOrd

abbrev NormRule := Rule NormRuleInfo

instance : ToFormat NormRule where
  format r := f!"[{r.extra.penalty}] {r.name}"

def defaultNormPenalty : Int := 1


/-! ### Safe and Almost Safe Rules -/

inductive Safety
  | safe
  | almostSafe
  deriving Inhabited

namespace Safety

instance : ToFormat Safety where
  format
    | safe => "safe"
    | almostSafe => "almostSafe"

end Safety

structure SafeRuleInfo where
  penalty : Int
  safety : Safety
  deriving Inhabited

instance : Ord SafeRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT SafeRuleInfo :=
  ltOfOrd

instance : LE SafeRuleInfo :=
  leOfOrd

abbrev SafeRule := Rule SafeRuleInfo

instance : ToFormat SafeRule where
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

abbrev UnsafeRule := Rule UnsafeRuleInfo

instance : ToFormat UnsafeRule where
  format r := f!"[{r.extra.successProbability.toHumanString}] {r.name}"


/-! ### Regular Rules -/

inductive RegularRule
  | safe (r : SafeRule)
  | «unsafe» (r : UnsafeRule)
  deriving Inhabited, BEq

namespace RegularRule

instance : ToFormat RegularRule where
  format
    | safe r => format r
    | «unsafe» r => format r

def successProbability : RegularRule → Percent
  | safe r => Percent.hundred
  | «unsafe» r => r.extra.successProbability

def isSafe : RegularRule → Bool
  | safe _ => true
  | «unsafe» _ => false

def isUnsafe : RegularRule → Bool
  | safe _ => false
  | «unsafe» _ => true

@[inline]
def withRule (f : ∀ {α}, Rule α → β) : RegularRule → β
  | safe r => f r
  | «unsafe» r => f r

def name (r : RegularRule) : RuleName :=
  r.withRule (·.name)

def indexingMode (r : RegularRule) : IndexingMode :=
  r.withRule (·.indexingMode)

def usesBranchState (r : RegularRule) : Bool :=
  r.withRule (·.usesBranchState)

def tac (r : RegularRule) : RuleTacDescr :=
  r.withRule (·.tac)

end RegularRule


/-! ### Normalisation Simp Rules -/

structure NormSimpRule where
  name : RuleName
  entries : Array SimpEntry

namespace NormSimpRule

instance : BEq NormSimpRule where
  beq r s := r.name == s.name

instance : Hashable NormSimpRule where
  hash r := hash r.name

end NormSimpRule
