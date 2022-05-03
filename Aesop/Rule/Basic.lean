/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule.Name
import Aesop.RuleIndex.Basic
import Aesop.RuleTac.Basic

open Lean

namespace Aesop

structure Rule (α : Type) where
  name : RuleName
  indexingMode : IndexingMode
  usesBranchState : Bool
  extra : α
  tac : RuleTacDescr
  deriving Inhabited

namespace Rule

instance : BEq (Rule α) where
  beq r s := r.name == s.name

instance : Ord (Rule α) where
  compare r s := compare r.name s.name

instance : Hashable (Rule α) where
  hash r := hash r.name

def compareByPriority [Ord α] (r s : Rule α) : Ordering :=
  compare r.extra s.extra

def compareByName (r s : Rule α) : Ordering :=
  r.name.compare s.name

def compareByPriorityThenName [Ord α] (r s : Rule α) : Ordering :=
  match compareByPriority r s with
  | Ordering.eq => compareByName r s
  | ord => ord

@[inline]
protected def map (f : α → β) (r : Rule α) : Rule β :=
  { r with extra := f r.extra }

@[inline]
protected def mapM [Monad m] (f : α → m β) (r : Rule α) : m (Rule β) :=
  return { r with extra := ← f r.extra }

end Aesop.Rule
