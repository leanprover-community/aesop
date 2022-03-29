/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic
import Aesop.Rule.Name
import Aesop.Rule.Tac

open Lean

namespace Aesop

structure Rule' (α τ : Type) where
  name : RuleName
  indexingMode : IndexingMode
  usesBranchState : Bool
  extra : α
  tac : τ
  deriving Inhabited

namespace Rule'

instance : BEq (Rule' α τ) where
  beq r s := r.name == s.name

instance : Ord (Rule' α τ) where
  compare r s := compare r.name s.name

instance : Hashable (Rule' α τ) where
  hash r := hash r.name

def compareByPriority [Ord α] (r s : Rule' α τ) : Ordering :=
  compare r.extra s.extra

def compareByName (r s : Rule' α τ) : Ordering :=
  r.name.compare s.name

def compareByPriorityThenName [Ord α] (r s : Rule' α τ) : Ordering :=
  match compareByPriority r s with
  | Ordering.eq => compareByName r s
  | ord => ord

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

@[inline]
def tacToDescr (r : Rule' α RuleTacWithBuilderDescr) :
    Rule' α (Option GlobalRuleTacBuilderDescr) :=
  r.mapTac (·.descr)

end Rule'

end Aesop
