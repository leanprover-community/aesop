/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Rule.Basic
import Aesop.Percent

namespace Aesop

open Lean
open Lean.Meta

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

instance : ToString NormRule where
  toString r := s!"[{r.extra.penalty}] {r.name}"

def defaultNormPenalty : Int := 1

def defaultSimpRulePriority : Int := eval_prio default


/-! ### Safe and Almost Safe Rules -/

inductive Safety
  | safe
  | almostSafe
  deriving Inhabited

namespace Safety

instance : ToString Safety where
  toString
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

instance : ToString SafeRule where
  toString r := s!"[{r.extra.penalty}/{r.extra.safety}] {r.name}"

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

instance : ToString UnsafeRule where
  toString r := s!"[{r.extra.successProbability.toHumanString}] {r.name}"

def defaultSuccessProbability : Percent := .fifty


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
  | safe _ => Percent.hundred
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

def tac (r : RegularRule) : RuleTacDescr :=
  r.withRule (·.tac)

end RegularRule


/-! ### Normalisation Simp Rules -/

/--
A global rule for the norm simplifier. Each `SimpEntry` represents a member
of the simp set, e.g. a declaration whose type is an equality or a smart
unfolding theorem for a declaration.
-/
structure NormSimpRule where
  name : RuleName
  entries : Array SimpEntry
  deriving Inhabited

namespace NormSimpRule

instance : BEq NormSimpRule where
  beq r s := r.name == s.name

instance : Hashable NormSimpRule where
  hash r := hash r.name

end NormSimpRule


/--
A local rule for the norm simplifier.
-/
structure LocalNormSimpRule where
  id : Name
  simpTheorem : Term
  deriving Inhabited

namespace LocalNormSimpRule

instance : BEq LocalNormSimpRule where
  beq r₁ r₂ := r₁.id == r₂.id

instance : Hashable LocalNormSimpRule where
  hash r := hash r.id

def name (r : LocalNormSimpRule) : RuleName :=
  { name := r.id, scope := .local, builder := .simp, phase := .norm }

end LocalNormSimpRule


structure UnfoldRule where
  decl : Name
  unfoldThm? : Option Name
  deriving Inhabited

namespace UnfoldRule

instance : BEq UnfoldRule where
  beq r s := r.decl == s.decl

instance : Hashable UnfoldRule where
  hash r := hash r.decl

def name (r : UnfoldRule) : RuleName :=
  { name := r.decl, builder := .unfold, phase := .norm, scope := .global }

end Aesop.UnfoldRule
