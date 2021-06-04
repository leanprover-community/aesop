/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

universe u

namespace Aesop

/-! ## Unsafe Construction of `MutableAndOrTree` -/

namespace MutableAndOrTree.Internal

-- Workaround for a compiler bug(?).
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Defining.20mutable.20rose.20trees
private abbrev Ref σ α := ST.Ref σ α

-- Note that α and ω are not really parameters, and indeed the mk constructor
-- has type `{α ω : Type} → ...`. But if we change the signature to
--
--     MutableAndOrTreeImp (σ : Type) : Type → Type → Type
--
-- the compiler fails.
unsafe inductive MutableAndOrTreeImp (σ α ω : Type) : Type
| mk
  (payload : α)
  (parent : Option (Ref σ (MutableAndOrTreeImp σ ω α)))
  (children : Array (Ref σ (MutableAndOrTreeImp σ ω α)))

structure MutableAndOrTreeSpec (σ) where
  MutableAndOrTree : Type → Type → Type
  construct :
    α →
    Option (ST.Ref σ (MutableAndOrTree ω α)) →
    Array (ST.Ref σ (MutableAndOrTree ω α)) →
    MutableAndOrTree α ω
  payload : MutableAndOrTree α ω → α
  parent : MutableAndOrTree α ω → Option (Ref σ (MutableAndOrTree ω α))
  children : MutableAndOrTree α ω → Array (ST.Ref σ (MutableAndOrTree ω α))

open MutableAndOrTreeImp in
unsafe def MutableAndOrTreeSpecImp σ : MutableAndOrTreeSpec σ where
  MutableAndOrTree := MutableAndOrTreeImp σ
  construct := mk
  payload := fun t => match t with | (mk x _ _) => x
  -- The syntax `payload | (mk x _ _) => x` doesn't work here for some reason.
  parent := fun t => match t with | (mk _ x _) => x
  children := fun t => match t with | (mk _ _ x) => x

@[implementedBy MutableAndOrTreeSpecImp]
constant mutableAndOrTreeSpec σ : MutableAndOrTreeSpec σ := {
  MutableAndOrTree := fun α ω => α
  construct := fun a _ _ => a
  payload := fun a => a
  parent := fun _ => arbitrary
  children := fun _ => arbitrary
}

end MutableAndOrTree.Internal

open MutableAndOrTree.Internal (mutableAndOrTreeSpec)


/-! ## `MutableAndOrTree` -/

def MutableAndOrTree (σ α ω : Type) : Type :=
  (mutableAndOrTreeSpec σ).MutableAndOrTree α ω

abbrev MAOT := MutableAndOrTree

abbrev MAOTRef σ α ω := ST.Ref σ (MAOT σ α ω)

namespace MutableAndOrTree

/-! ### Constructors -/

@[inline]
def mk : α → Option (MAOTRef σ ω α) → Array (MAOTRef σ ω α) → MAOT σ α ω :=
  (mutableAndOrTreeSpec σ).construct

instance [Inhabited α] : Inhabited (MutableAndOrTree σ α ω) where
  default := mk arbitrary none #[]

/-! ### Getters -/

section Getters

variable (t : MAOT σ α ω)

@[inline]
def payload : α :=
  (mutableAndOrTreeSpec σ).payload t

@[inline]
def parent : Option (MAOTRef σ ω α) :=
  (mutableAndOrTreeSpec σ).parent t

@[inline]
def children : Array (MAOTRef σ ω α) :=
  (mutableAndOrTreeSpec σ).children t

end Getters

/-! ### Setters -/

@[inline]
def setPayload (a : α) (t : MAOT σ α ω) : MAOT σ α ω :=
  mk a (parent t) (children t)

@[inline]
def setParent (parent : Option (MAOTRef σ ω α)) (t : MAOT σ α ω) : MAOT σ α ω :=
  mk (payload t) parent (children t)

@[inline]
def setChildren (children : Array (MAOTRef σ ω α)) (t : MAOT σ α ω) :
    MAOT σ α ω :=
  mk (payload t) (parent t) children

/-! ### 'Lenses' -/

@[inline]
def modifyPayload (f : α → α) (t : MAOT σ α ω) : MAOT σ α ω :=
  t.setPayload $ f t.payload

@[inline]
def modifyParent (f : Option (MAOTRef σ ω α) → Option (MAOTRef σ ω α))
    (t : MAOT σ α ω) : MAOT σ α ω :=
  t.setParent $ f t.parent

@[inline]
def modifyChildren (f : Array (MAOTRef σ ω α) → Array (MAOTRef σ ω α))
    (t : MAOT σ α ω) : MAOT σ α ω :=
  t.setChildren $ f t.children

/-! ### Traversals -/

variable {σ m} [Monad m] [MonadLiftT (ST σ) m]

partial def visitDown (fα : MAOTRef σ α ω → m Bool) (fω : MAOTRef σ ω α → m Bool)
    (tref : MAOTRef σ α ω) : m Unit := do
  let continue? ← fα tref
  if continue? then
    (← tref.get).children.forM $ visitDown fω fα

@[inline]
def visitDown' (fα : MAOTRef σ α ω → m Bool) (fω : MAOTRef σ ω α → m Bool) :
    Sum (MAOTRef σ α ω) (MAOTRef σ ω α) → m Unit
  | Sum.inl tref => visitDown fα fω tref
  | Sum.inr tref => visitDown fω fα tref

partial def visitUp (fα : MAOTRef σ α ω → m Bool) (fω : MAOTRef σ ω α → m Bool)
    (tref : MAOTRef σ α ω) : m Unit := do
  let continue? ← fα tref
  if continue? then
    match (← tref.get).parent with
    | none => return ()
    | some parent => visitUp fω fα parent

@[inline]
def visitUp'
    (fα : MAOTRef σ α ω → m Bool) (fω : MAOTRef σ ω α → m Bool) :
    Sum (MAOTRef σ α ω) (MAOTRef σ ω α) → m Unit
  | Sum.inl tref => visitUp fα fω tref
  | Sum.inr tref => visitUp fω fα tref

/-! ### Miscellaneous -/

@[inline]
def addChild (c : MAOTRef σ ω α) (t : MAOT σ α ω) : MAOT σ α ω :=
  t.modifyChildren $ λ cs => cs.push c

def siblings (tref : MAOTRef σ α ω) : m (Array (MAOTRef σ α ω)) := do
  let t ← tref.get
  let (some parent) ← pure t.parent | return #[]
  let children := (← parent.get).children
  return (← children.filterM λ cref => return not (← cref.ptrEq tref))

end MutableAndOrTree
end Aesop
