/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Data.Array.Merge
import Lean.Message

open Lean Std

namespace Aesop

structure UnorderedArraySet (α) [BEq α] where
  private mk ::
  private rep : Array α
  deriving Inhabited

namespace UnorderedArraySet

variable [BEq α]

/-- O(1) -/
protected def empty : UnorderedArraySet α :=
  ⟨#[]⟩

instance : EmptyCollection (UnorderedArraySet α) :=
  ⟨UnorderedArraySet.empty⟩

/-- O(1) -/
protected def singleton (a : α) : UnorderedArraySet α :=
  ⟨#[a]⟩

/-- O(n) -/
def insert (x : α) : UnorderedArraySet α → UnorderedArraySet α
  | ⟨rep⟩ => if rep.contains x then ⟨rep⟩ else ⟨rep.push x⟩

/-- Precondition: `xs` contains no duplicates. -/
protected def ofDeduplicatedArray (xs : Array α) : UnorderedArraySet α :=
  ⟨xs⟩

/-- Precondition: `xs` is sorted. -/
protected def ofSortedArray (xs : Array α) : UnorderedArraySet α :=
  ⟨xs.dedupSorted⟩

set_option linter.unusedVariables false in
/-- O(n*log(n)) -/
protected def ofArray [ord : Ord α] (xs : Array α) :
    UnorderedArraySet α :=
  ⟨xs.sortDedup⟩

/-- O(n^2) -/
protected def ofArraySlow (xs : Array α) : UnorderedArraySet α :=
  xs.foldl (init := {}) λ s x => s.insert x

protected def ofHashSet [Hashable α] (xs : Std.HashSet α) : UnorderedArraySet α :=
  ⟨xs.toArray⟩

protected def ofPersistentHashSet [Hashable α] (xs : PersistentHashSet α) : UnorderedArraySet α :=
  ⟨xs.fold (init := #[]) λ as a => as.push a⟩

protected def toArray (s : UnorderedArraySet α) : Array α :=
  s.rep

/-- O(n) -/
def erase (x : α) (s : UnorderedArraySet α) : UnorderedArraySet α :=
  ⟨s.rep.erase x⟩

/-- O(n) -/
def filterM [Monad m] (p : α → m Bool) (s : UnorderedArraySet α) :
    m (UnorderedArraySet α) :=
  return ⟨← s.rep.filterM p⟩

/-- O(n) -/
def filter (p : α → Bool) (s : UnorderedArraySet α) : UnorderedArraySet α :=
  ⟨s.rep.filter p⟩

/-- O(n*m) -/
def merge (s t : UnorderedArraySet α) : UnorderedArraySet α :=
  ⟨s.rep.mergeUnsortedDedup t.rep⟩

instance : Append (UnorderedArraySet α) :=
  ⟨merge⟩

/-- O(n) -/
def contains (x : α) (s : UnorderedArraySet α) : Bool :=
  s.rep.contains x

/-- O(n) -/
def foldM [Monad m] (f : σ → α → m σ) (init : σ) (s : UnorderedArraySet α) :
    m σ :=
  s.rep.foldlM f init

instance : ForIn m (UnorderedArraySet α) α where
  forIn s := s.rep.forIn

/-- O(n) -/
def fold (f : σ → α → σ) (init : σ) (s : UnorderedArraySet α) : σ :=
  s.rep.foldl f init

def partition (f : α → Bool) (s : UnorderedArraySet α) :
    (UnorderedArraySet α × UnorderedArraySet α) :=
  let (xs, ys) := s.rep.partition f
  (⟨xs⟩, ⟨ys⟩)

/-- O(1) -/
def size (s : UnorderedArraySet α) : Nat :=
  s.rep.size

/-- O(1) -/
def isEmpty (s : UnorderedArraySet α) : Bool :=
  s.rep.isEmpty

/-- O(n) -/
def anyM [Monad m] (p : α → m Bool) (s : UnorderedArraySet α) (start := 0)
    (stop := s.size) : m Bool :=
  s.rep.anyM p start stop

/-- O(n) -/
def any (p : α → Bool) (s : UnorderedArraySet α) (start := 0) (stop := s.size) :
    Bool :=
  s.rep.any p start stop

/-- O(n) -/
def allM [Monad m] (p : α → m Bool) (s : UnorderedArraySet α) (start := 0)
    (stop := s.size) : m Bool :=
  s.rep.allM p start stop

/-- O(n) -/
def all (p : α → Bool) (s : UnorderedArraySet α) (start := 0) (stop := s.size) :
    Bool :=
  s.rep.all p start stop

instance [ToString α] : ToString (UnorderedArraySet α) where
  toString s := toString s.rep

instance [ToFormat α] : ToFormat (UnorderedArraySet α) where
  format s := format s.rep

instance [ToMessageData α] : ToMessageData (UnorderedArraySet α) where
  toMessageData s := toMessageData s.rep

end Aesop.UnorderedArraySet
