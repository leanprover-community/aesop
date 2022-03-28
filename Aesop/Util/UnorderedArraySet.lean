/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic

open Lean

namespace Aesop

structure UnorderedArraySet (α) [BEq α] where
  private mk ::
  private rep : Array α

namespace UnorderedArraySet

variable [BEq α]

/-- O(1) -/
protected def empty : UnorderedArraySet α :=
  ⟨#[]⟩

instance : EmptyCollection (UnorderedArraySet α) :=
  ⟨UnorderedArraySet.empty⟩

/-- O(n) -/
def insert (x : α) : UnorderedArraySet α → UnorderedArraySet α
  | ⟨rep⟩ => if rep.contains x then ⟨rep⟩ else ⟨rep.push x⟩

/-- Precondition: `xs` contains no duplicates. -/
protected def ofDeduplicatedArray (xs : Array α) : UnorderedArraySet α :=
  ⟨xs⟩

/-- Precondition: `xs` is sorted. -/
protected def ofSortedArray (xs : Array α) : UnorderedArraySet α :=
  ⟨xs.deduplicateSorted⟩

/-- O(n*log(n)) -/
protected def ofArrayOrd [ord : Ord α] [Inhabited α] (xs : Array α) :
    UnorderedArraySet α :=
  ⟨xs.deduplicate⟩

/-- O(n^2) -/
protected def ofArray (xs : Array α) : UnorderedArraySet α :=
  xs.foldl (init := {}) λ s x => s.insert x

protected def toArray (s : UnorderedArraySet α) : Array α :=
  s.rep

/-- O(n) -/
def erase (x : α) (s : UnorderedArraySet α) : UnorderedArraySet α :=
  ⟨s.rep.erase x⟩

/-- O(n) -/
def filter (p : α → Bool) (s : UnorderedArraySet α) : UnorderedArraySet α :=
  ⟨s.rep.filter p⟩

/-- O(n) -/
def contains (x : α) (s : UnorderedArraySet α) : Bool :=
  s.rep.contains x

/-- O(n) -/
def foldM [Monad m] (f : σ → α → m σ) (init : σ) (s : UnorderedArraySet α) :
    m σ :=
  s.rep.foldlM f init

instance [Monad m] : ForIn m (UnorderedArraySet α) α where
  forIn s := s.rep.forIn

/-- O(n) -/
def fold (f : σ → α → σ) (init : σ) (s : UnorderedArraySet α) : σ :=
  s.rep.foldl f init

/-- O(1) -/
def size (s : UnorderedArraySet α) : Nat :=
  s.rep.size

/-- O(1) -/
def isEmpty (s : UnorderedArraySet α) : Bool :=
  s.rep.isEmpty

instance : BEq (UnorderedArraySet α) where
  beq s t := s.rep.equalSet t.rep

instance [ToString α] : ToString (UnorderedArraySet α) where
  toString s := toString s.rep

instance [ToFormat α] : ToFormat (UnorderedArraySet α) where
  format s := format s.rep

instance [ToMessageData α] : ToMessageData (UnorderedArraySet α) where
  toMessageData s := toMessageData s.rep

end Aesop.UnorderedArraySet
