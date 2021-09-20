/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic
import Aesop.Rule.Tac

open Lean

namespace Aesop

/- The rules in a rule set should be uniquely identified by their name. -/
structure Rule' (α τ : Type) where
  name : Name
  indexingMode : IndexingMode
  usesBranchState : Bool
  extra : α
  tac : τ
  deriving Inhabited

namespace Rule'

instance : BEq (Rule' α τ) where
  beq r s := r.name == s.name

instance [Ord α] : Ord (Rule' α τ) :=
  Ord.lexicographic
    ⟨λ r s => compare r.extra s.extra⟩
    ⟨λ r s => r.name.quickCmp s.name⟩

instance [Ord α] : LT (Rule' α τ) :=
  ltOfOrd

instance [Ord α] : LE (Rule' α τ) :=
  leOfOrd

@[inline]
def map (f : α → β) (g : τ → ι) (r : Rule' α τ) : Rule' β ι :=
  { r with tac := g r.tac, extra := f r.extra }

@[inline]
def mapExtra (f : α → β) (r : Rule' α τ) : Rule' β τ :=
  map f id r

@[inline]
def mapTac (f : τ → ι) (r : Rule' α τ) : Rule' α ι :=
  map id f r

@[inline]
def mapM [Monad m] (f : α → m β) (g : τ → m ι) (r : Rule' α τ) : m (Rule' β ι) :=
  return { r with tac := (← g r.tac), extra := (← f r.extra) }

@[inline]
def mapExtraM [Monad m] (f : α → m β) (r : Rule' α τ) : m (Rule' β τ) :=
  mapM f pure r

@[inline]
def mapTacM [Monad m] (f : τ → m ι) (r : Rule' α τ) : m (Rule' α ι) :=
  mapM pure f r

def tacToDescr (r : Rule' α SerializableRuleTac) :
    Rule' α (Option RuleTacDescr) :=
  r.mapTac (·.descr)

def descrToTac (r : Rule' α RuleTacDescr) : MetaM (Rule' α SerializableRuleTac) :=
  return { r with tac := (← r.tac.toRuleTac) }

end Rule'

end Aesop
