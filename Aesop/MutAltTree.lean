/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

universe u

namespace Aesop

/-! ## Unsafe Construction of `MutAltTree` -/

namespace MutAltTree.Internal

-- Workaround for a compiler bug(?).
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Defining.20mutable.20rose.20trees
private abbrev Ref σ α := ST.Ref σ α

-- Note that α and ω are not really parameters, and indeed the mk constructor
-- has type `{α ω : Type} → ...`. But if we change the signature to
--
--     MutAltTreeImp (σ : Type) : Type → Type → Type
--
-- the compiler fails.
unsafe inductive MutAltTreeImp (σ α ω : Type) : Type
| mk
  (payload : α)
  (parent : Option (Ref σ (MutAltTreeImp σ ω α)))
  (children : Array (Ref σ (MutAltTreeImp σ ω α)))

structure MutAltTreeSpec (σ) where
  MutAltTree : Type → Type → Type
  construct :
    α →
    Option (ST.Ref σ (MutAltTree ω α)) →
    Array (ST.Ref σ (MutAltTree ω α)) →
    MutAltTree α ω
  payload : MutAltTree α ω → α
  parent : MutAltTree α ω → Option (Ref σ (MutAltTree ω α))
  children : MutAltTree α ω → Array (ST.Ref σ (MutAltTree ω α))

open MutAltTreeImp in
unsafe def MutAltTreeSpecImp σ : MutAltTreeSpec σ where
  MutAltTree := MutAltTreeImp σ
  construct := mk
  payload := fun t => match t with | (mk x _ _) => x
  -- The syntax `payload | (mk x _ _) => x` doesn't work here for some reason.
  parent := fun t => match t with | (mk _ x _) => x
  children := fun t => match t with | (mk _ _ x) => x

@[implementedBy MutAltTreeSpecImp]
constant mutAltTreeSpec σ : MutAltTreeSpec σ := {
  MutAltTree := fun α ω => α
  construct := fun a _ _ => a
  payload := fun a => a
  parent := fun _ => arbitrary
  children := fun _ => arbitrary
}

end MutAltTree.Internal

open MutAltTree.Internal (mutAltTreeSpec)


/-! ## `MutAltTree` -/

def MutAltTree (σ α ω : Type) : Type :=
  (mutAltTreeSpec σ).MutAltTree α ω

abbrev MATRef σ α ω := ST.Ref σ (MutAltTree σ α ω)

namespace MutAltTree

/-! ### Constructors -/

@[inline]
def mk : α → Option (MATRef σ ω α) → Array (MATRef σ ω α) → MutAltTree σ α ω :=
  (mutAltTreeSpec σ).construct

instance [Inhabited α] : Inhabited (MutAltTree σ α ω) where
  default := mk arbitrary none #[]

/-! ### Getters -/

section Getters

variable (t : MutAltTree σ α ω)

@[inline]
def payload : α :=
  (mutAltTreeSpec σ).payload t

@[inline]
def parent : Option (MATRef σ ω α) :=
  (mutAltTreeSpec σ).parent t

@[inline]
def children : Array (MATRef σ ω α) :=
  (mutAltTreeSpec σ).children t

end Getters

/-! ### Setters -/

@[inline]
def setPayload (a : α) (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  mk a (parent t) (children t)

@[inline]
def setParent (parent : Option (MATRef σ ω α)) (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  mk (payload t) parent (children t)

@[inline]
def setChildren (children : Array (MATRef σ ω α)) (t : MutAltTree σ α ω) :
    MutAltTree σ α ω :=
  mk (payload t) (parent t) children

/-! ### 'Lenses' -/

@[inline]
def modifyPayload (f : α → α) (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  t.setPayload $ f t.payload

@[inline]
def modifyParent (f : Option (MATRef σ ω α) → Option (MATRef σ ω α))
    (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  t.setParent $ f t.parent

@[inline]
def modifyChildren (f : Array (MATRef σ ω α) → Array (MATRef σ ω α))
    (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  t.setChildren $ f t.children

/-! ### Traversals -/

variable {σ m} [Monad m] [MonadLiftT (ST σ) m]

partial def visitDown (fα : MATRef σ α ω → m Bool) (fω : MATRef σ ω α → m Bool)
    (tref : MATRef σ α ω) : m Unit := do
  let continue? ← fα tref
  if continue? then
    (← tref.get).children.forM $ visitDown fω fα

@[inline]
def visitDown' (fα : MATRef σ α ω → m Bool) (fω : MATRef σ ω α → m Bool) :
    Sum (MATRef σ α ω) (MATRef σ ω α) → m Unit
  | Sum.inl tref => visitDown fα fω tref
  | Sum.inr tref => visitDown fω fα tref

partial def visitUp (fα : MATRef σ α ω → m Bool) (fω : MATRef σ ω α → m Bool)
    (tref : MATRef σ α ω) : m Unit := do
  let continue? ← fα tref
  if continue? then
    match (← tref.get).parent with
    | none => return ()
    | some parent => visitUp fω fα parent

@[inline]
def visitUp'
    (fα : MATRef σ α ω → m Bool) (fω : MATRef σ ω α → m Bool) :
    Sum (MATRef σ α ω) (MATRef σ ω α) → m Unit
  | Sum.inl tref => visitUp fα fω tref
  | Sum.inr tref => visitUp fω fα tref

/-! ### Miscellaneous -/

@[inline]
def addChild (c : MATRef σ ω α) (t : MutAltTree σ α ω) : MutAltTree σ α ω :=
  t.modifyChildren $ λ cs => cs.push c

def siblings (tref : MATRef σ α ω) : m (Array (MATRef σ α ω)) := do
  let t ← tref.get
  let (some parent) ← pure t.parent | return #[]
  let children := (← parent.get).children
  return (← children.filterM λ cref => return not (← cref.ptrEq tref))

end Aesop.MutAltTree
